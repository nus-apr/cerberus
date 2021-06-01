// Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
// Prophet
// 
// This file is part of Prophet.
// 
// Prophet is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// Prophet is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
#include "ProfileErrorLocalizer.h"
#include <clang/AST/ASTConsumer.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Basic/Diagnostic.h>
#include <clang/Rewrite/Core/Rewriter.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Frontend/FrontendPluginRegistry.h>
#include <clang/Lex/Lexer.h>
#include <llvm/Support/raw_ostream.h>
#include <sstream>
#include <fstream>
#include <assert.h>

#define PROFILER_INIT_FUNC "__prof_init"
#define PROFILER_TRACK_FUNC "__prof_track"

using namespace clang;

namespace {

std::string getFullPath(const std::string &path) {
    char tmp[PATH_MAX];
    char * ret = realpath(path.c_str(), tmp);
    if (ret != 0)
        return std::string(tmp);
    else
        return std::string("unkown_src_file");
}

typedef std::map<std::string, std::vector<std::string> > RewriteTextMapTy;

bool isExecCall(Decl* D) {
    if (!D) return false;
    FunctionDecl *FD = llvm::dyn_cast<FunctionDecl>(D);
    if (!FD || !FD->getDeclName().isIdentifier()) return false;
    std::string str = FD->getName();
    return str == "execl" || str == "execlp" || str == "execle" || str == "execv" || str == "execve" || str == "execvp" || str == "fexecve";
}

class ProfilerGenConsumer : public ASTConsumer {
    std::string outfile;
    RewriteTextMapTy rewriteTextMap;
    LocationIndex LI;

    class ProfilerGenVisitor : public RecursiveASTVisitor<ProfilerGenVisitor> {
        ASTContext *C;
        RewriteTextMapTy &M;
        std::vector<std::string> *cur_v;
        LocationIndex &LI;

    public:
        ProfilerGenVisitor(ASTContext *C, RewriteTextMapTy &M, LocationIndex &LI):
            C(C), M(M), cur_v(NULL), LI(LI) { }

        virtual bool TraverseCompoundStmt(CompoundStmt *CS) {
            if (cur_v) {
                for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                    Stmt* S = *it;
                    CallExpr *CE = llvm::dyn_cast<CallExpr>(S);
                    if (CE) {
                        Decl *D = CE->getCalleeDecl();
                        if (isExecCall(D)) {
                            cur_v->push_back("__prof_exit();");
                            continue;
                        }
                    }
                    SourceManager &M = C->getSourceManager();
                    SourceLocation loc = S->getLocStart();
                    SourceLocation expandLoc = M.getExpansionLoc(loc);
                    SourceLocation spellingLoc = M.getSpellingLoc(loc);

                    std::ostringstream sout;
                    size_t idx = LI.getIndexNo(getFullPath(M.getFilename(expandLoc)), M.getExpansionLineNumber(loc), M.getExpansionColumnNumber(loc),
                            getFullPath(M.getFilename(spellingLoc)), M.getSpellingLineNumber(loc), M.getSpellingColumnNumber(loc));
                    sout << "__prof_track(" << idx << ");";
                    /*sout << "__prof_track(\"" << std::string(M.getFilename(expandLoc)) << "\"," << M.getExpansionLineNumber(loc) \
                        << "," << M.getExpansionColumnNumber(loc) << ",\"" << std::string(M.getFilename(spellingLoc)) << "\"," \
                        << M.getSpellingLineNumber(loc) << "," << M.getSpellingColumnNumber(loc) << ");";*/

                    cur_v->push_back(sout.str());
                }
            }
            return RecursiveASTVisitor::TraverseCompoundStmt(CS);
        }

        virtual bool VisitIfStmt(IfStmt *IF) {
            if (IF == NULL) return true;
            Stmt* thenS = IF->getThen();
            Stmt* elseS = IF->getElse();
            if (thenS && !llvm::isa<CompoundStmt>(thenS)) {
                SourceManager &M = C->getSourceManager();
                SourceLocation loc = thenS->getLocStart();
                SourceLocation expandLoc = M.getExpansionLoc(loc);
                SourceLocation spellingLoc = M.getSpellingLoc(loc);
                std::ostringstream sout;
                size_t idx = LI.getIndexNo(getFullPath(M.getFilename(expandLoc)), M.getExpansionLineNumber(loc), M.getExpansionColumnNumber(loc),
                        getFullPath(M.getFilename(spellingLoc)), M.getSpellingLineNumber(loc), M.getSpellingColumnNumber(loc));
                sout << "__prof_track(" << idx << ");";
                if (cur_v)
                    cur_v->push_back(sout.str());
            }
            if (elseS && !llvm::isa<CompoundStmt>(elseS)) {
                SourceManager &M = C->getSourceManager();
                SourceLocation loc = elseS->getLocStart();
                SourceLocation expandLoc = M.getExpansionLoc(loc);
                SourceLocation spellingLoc = M.getSpellingLoc(loc);
                std::ostringstream sout;
                size_t idx = LI.getIndexNo(getFullPath(M.getFilename(expandLoc)), M.getExpansionLineNumber(loc), M.getExpansionColumnNumber(loc),
                        getFullPath(M.getFilename(spellingLoc)), M.getSpellingLineNumber(loc), M.getSpellingColumnNumber(loc));
                sout << "__prof_track(" << idx << ");";
                if (cur_v)
                    cur_v->push_back(sout.str());
            }
            return true;
        }

        virtual bool TraverseFunctionDecl(FunctionDecl *FD) {
            if (FD->getDeclName().isIdentifier() && FD->hasBody()) { // Some C++ will generate non-identifier func, wtf
                M[FD->getName()].clear();
                cur_v = &M[FD->getName()];
            }
            else
                cur_v = NULL;
            return RecursiveASTVisitor::TraverseFunctionDecl(FD);
        }
    };

public:
    ProfilerGenConsumer(const std::string &outfile, const std::string &indexfile): outfile(outfile), LI(indexfile) {
        rewriteTextMap.clear();
    }

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        TranslationUnitDecl *TD = Context.getTranslationUnitDecl();
        ProfilerGenVisitor V(&Context, rewriteTextMap, LI);
        V.TraverseDecl(TD);
        LI.writeBack();
        //Deserialize the text
        std::ofstream fout(outfile.c_str(), std::ofstream::out);
        assert(fout.is_open());
        fout << rewriteTextMap.size() << "\n";
        for (RewriteTextMapTy::iterator it = rewriteTextMap.begin(); it != rewriteTextMap.end(); ++it) {
            fout << it->first << "\n";
            std::vector<std::string> &v = it->second;
            fout << v.size() << "\n";
            for (size_t i = 0; i < v.size(); i++)
                fout << v[i] << "\n";
        }
        fout.close();
    }
};

class ProfilerGenAction : public PluginASTAction {
    std::string outfile;
    std::string indexfile;
public:
    virtual bool ParseArgs(const CompilerInstance &CI,
            const std::vector<std::string> &args) {
        if (args.size() >= 1)
            outfile = args[0];
        else
            outfile = "__rewrite.log";
        if (args.size() >= 2)
            indexfile = args[1];
        else
            indexfile = "__location.idx";
        //llvm::errs() << "Come here: " << args[0] << " " << args[1] << "\n";
        return true;
    }

    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, llvm::StringRef InFile) {
        // Remove the output, we are just doing the generation!
        CI.clearOutputFiles(false);
        return std::unique_ptr<ASTConsumer>(new ProfilerGenConsumer(outfile, indexfile));
    }
};

SourceLocation findTrueEndLoc(ASTContext &C, Stmt* S) {
    SourceLocation origEnd = S->getLocEnd();
    SourceManager &SM = C.getSourceManager();
    const char * stmtBuf = SM.getCharacterData(origEnd);
    const char * semiBuf = strchr(stmtBuf, ';');
    while (semiBuf != NULL) {
        const char* p = stmtBuf;
        size_t cnt = 0;
        bool lastspecial = false;
        while (p != semiBuf) {
            if ((*p == '"') && !lastspecial)
                cnt++;
            lastspecial = ((*p == '\'') || (*p == '\\'));
            p++;
        }
        if ((cnt & 1) == 0)
            break;
        else {
            semiBuf++;
            semiBuf = strchr(semiBuf, ';');
        }
    }
    const char * bracketBuf = strchr(stmtBuf, '}');
    if (semiBuf == NULL)
        return origEnd;
    size_t offset = semiBuf - stmtBuf + 1;
    size_t another_offset = bracketBuf - stmtBuf + 1;
    if (another_offset < offset)
        return origEnd;
    return origEnd.getLocWithOffset(offset);
}

class ProfilerRewriteConsumer : public ASTConsumer {
    std::string outfile;
    RewriteTextMapTy M;

    class ProfilerRewriteVisitor : public RecursiveASTVisitor<ProfilerRewriteVisitor> {
        ASTContext &C;
        Rewriter &R;
        RewriteTextMapTy &M;
        std::vector<std::string> *cur_v;
        size_t cur_cnt;
    public:
        ProfilerRewriteVisitor(ASTContext &C, Rewriter &R, RewriteTextMapTy &M): C(C), R(R), M(M), cur_v(NULL) { }

        virtual bool TraverseCompoundStmt(CompoundStmt *CS) {
            if (cur_v)
                if (cur_v->size() != 0) {
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                        Stmt* S = *it;
                        // FIXME: WTF
                        if (cur_cnt >= cur_v->size())
                            return true;
                        assert(cur_cnt < cur_v->size());
                        R.InsertText(S->getLocStart(), cur_v->at(cur_cnt) + "\n", false, true);
                        cur_cnt ++;
                    }
                }
            return RecursiveASTVisitor::TraverseCompoundStmt(CS);
        }

        virtual bool VisitIfStmt(IfStmt *IF) {
            if (IF == NULL) return true;
            if (!cur_v) return true;
            Stmt* thenS = IF->getThen();
            Stmt* elseS = IF->getElse();
            if (thenS && !llvm::isa<CompoundStmt>(thenS)) {
                // FIXME: WTF
                if (cur_cnt >= cur_v->size())
                    return true;
                assert(cur_cnt < cur_v->size());
                R.InsertText(thenS->getLocStart(), std::string("{") + cur_v->at(cur_cnt) + "\n", false, true);
                SourceLocation pastSemiLoc = findTrueEndLoc(C, thenS);
                assert(!pastSemiLoc.isInvalid());
                R.InsertTextAfter(pastSemiLoc, "}");
                cur_cnt ++;
            }
            if (elseS && !llvm::isa<CompoundStmt>(elseS)) {
                // FIXME: WTF
                if (cur_cnt >= cur_v->size())
                    return true;
                assert(cur_cnt < cur_v->size());
                R.InsertText(elseS->getLocStart(), std::string("{") + cur_v->at(cur_cnt) + "\n", false, true);
                SourceLocation pastSemiLoc = findTrueEndLoc(C, elseS);
                assert(! pastSemiLoc.isInvalid());
                R.InsertTextAfter(pastSemiLoc, "}");
                cur_cnt ++;
            }
            return true;
        }

        virtual bool TraverseFunctionDecl(FunctionDecl *FD)  {
            /* Not sure this is right, because the tokenized style of locations in clang
             * SourceManager &SM = C.getSourceManager();
            SourceLocation loc = FD->getLocStart();
            SourceLocation spellLoc = SM.getSpellingLoc(loc);
            std::string filename = SM.getFilename(spellLoc);
            if ((filename.size() > 5) && (filename.substr(0, 5) == "/usr/"))
                return true;*/
            if (FD->getDeclName().isIdentifier() && M.count(FD->getName()))
                cur_v = &M[FD->getName()];
            else
                cur_v = NULL;
            cur_cnt = 0;
            bool ret = RecursiveASTVisitor::TraverseFunctionDecl(FD);
            if (FD->getDeclName().isIdentifier() && FD->getName() == "main") {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(FD->getBody());
                R.InsertText((*CS->body_begin())->getLocStart(), "__prof_init();\n", false, true);
            }
            return ret;
        }
    };

public:
    ProfilerRewriteConsumer(const std::string textfile, const std::string outfile): outfile(outfile) {
        M.clear();
        std::ifstream fin(textfile.c_str(), std::ifstream::in);
        size_t n;
        fin >> n;
        for (size_t i = 0; i < n; i++) {
            std::string funcname;
            fin >> funcname;
            M[funcname].clear();
            size_t m;
            fin >> m;
            char c = fin.peek();
            std::string line;
            if (c == ' ' || c == '\n' || c == '\t')
                std::getline(fin, line);
            for (size_t j = 0; j < m; j++) {
                std::getline(fin, line);
                M[funcname].push_back(line);
            }
        }
    }

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        Rewriter R;
        SourceManager &SM = Context.getSourceManager();
        R.setSourceMgr(SM, Context.getLangOpts());
        ProfilerRewriteVisitor V(Context, R, M);
        V.TraverseDecl(Context.getTranslationUnitDecl());
        RewriteBuffer &buf = R.getEditBuffer(SM.getMainFileID());
        std::ofstream fout(outfile.c_str(), std::ofstream::out);
        assert(fout.is_open());
        fout << "#include \"_prophet_profile.h\"\n";
        fout << std::string(buf.begin(), buf.end());
        fout.close();
    }
};

class ProfilerRewriteAction : public PluginASTAction {
    std::string textfile;
    std::string outfile;
public:
    virtual bool ParseArgs(const CompilerInstance &CI,
            const std::vector<std::string> &args) {
        if (args.size() >= 1)
            textfile = args[0];
        else
            textfile = "__rewrite.log";
        if (args.size() >= 2)
            outfile = args[1];
        else
            outfile = "a.out";
        return true;
    }

    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, llvm::StringRef InFile) {
        CI.clearOutputFiles(false);
        return std::unique_ptr<ASTConsumer>(new ProfilerRewriteConsumer(textfile, outfile));
    }
};

}

static FrontendPluginRegistry::Add<ProfilerGenAction> X("err-profiler-gen", "prophet error localization profile gen");
static FrontendPluginRegistry::Add<ProfilerRewriteAction> Y("err-profiler-rewrite", "prophet error localization profile rewrite");
