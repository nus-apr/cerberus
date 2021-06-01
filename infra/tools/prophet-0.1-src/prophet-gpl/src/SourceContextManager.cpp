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
#include "SourceContextManager.h"
#include "LocalAnalyzer.h"
#include "BenchProgram.h"
#include "RepairSearchEngine.h"
#include "GlobalAnalyzer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"

const char* HANDLER_PREFIX =
    "int __get_mutant(); "
    "int __is_neg(int, ...); "
    "int __abst_hole(); ";
const char* MEMSET_PREFIX =
    "void* memset(void*, int, unsigned long); ";

using namespace clang;

namespace {

class AllStmtVisitor : public RecursiveASTVisitor<AllStmtVisitor> {
    std::set<Stmt*> &stmts;
public:
    AllStmtVisitor(std::set<Stmt*> &stmts): stmts(stmts) { }

    bool TraverseStmt(Stmt* s) {
        if (s == NULL) return true;
        stmts.insert(s);
        bool ret = RecursiveASTVisitor::TraverseStmt(s);
        return ret;
    }
};

}

SourceContextManager::~SourceContextManager() {
/*    for (std::map<std::string, clang::ASTUnit*>::iterator it = unitMap.begin(); it != unitMap.end(); ++it)
        delete it->second;*/
    for (std::map<ASTLocTy, LocalAnalyzer*>::iterator it = localAnalyzerMap.begin(); it != localAnalyzerMap.end(); ++it)
        delete it->second;
    for (std::map<ASTContext*, GlobalAnalyzer*>::iterator it = globalAnalyzerMap.begin(); it != globalAnalyzerMap.end(); ++it)
        delete it->second;
}

ASTContext *SourceContextManager::getSourceContext(const std::string &src_file) {
    assert(!is_header(src_file));
    if (unitMap.count(src_file) == 0) {
        assert(P);
        fetch(src_file);
    }
    return &(unitMap[src_file]->getASTContext());
}

static inline ImplicitCastExpr* createFExpr(ASTContext &ctxt, FunctionDecl *FD) {
    DeclRefExpr *FRef = DeclRefExpr::Create(ctxt, NestedNameSpecifierLoc(), SourceLocation(),
            FD, false, SourceLocation(), FD->getType(), VK_RValue);
    return ImplicitCastExpr::Create(ctxt, ctxt.getDecayedType(FD->getType()), CK_FunctionToPointerDecay,
            FRef, 0, VK_RValue);
}

/*static inline CallExpr* createCallExpr(ASTContext &ctxt, FunctionDecl *FD) {
    ImplicitCastExpr *FCast = createFExpr(ctxt, FD);
    return new(ctxt) CallExpr(ctxt, FCast, ArrayRef<Expr*>(), ctxt.IntTy, VK_RValue, SourceLocation());
}*/

void SourceContextManager::fetch(const std::string &file) {
    std::string code;
    assert( file.size() > 1);
    std::string fullpath;
    if (file[0] == '/')
        fullpath = file;
    else
        fullpath = P->getSrcdir() + "/" + file;
    if (!readCodeToString(fullpath, code)) {
        fprintf(stderr, "Failed to read the file %s\n", fullpath.c_str());
        assert(0);
    }

    if (!is_header(file)) {
        std::string prefix = "";
        // This is the fix some strange compile complain about the memset
        if ((code.find("ifdef") != std::string::npos) ||
            ((code.find("memset") == std::string::npos) && (code.find("string.h") == std::string::npos)))
            prefix = std::string(HANDLER_PREFIX) + MEMSET_PREFIX;
        else
            prefix = std::string(HANDLER_PREFIX);
        if (get_ext(file) == "cpp" || get_ext(file) == "cc")
            prefix = "extern \"C\" { " + std::string(HANDLER_PREFIX) + "}";
        code = prefix + "\n" + code;
        unitMap[file] = P->buildClangASTUnit(file, code);
        std::unique_ptr<clang::ASTUnit> &unit = unitMap[file];

        ASTContext &ctxt = unit->getASTContext();
        globalAnalyzerMap[&ctxt] = new GlobalAnalyzer(ctxt, file);
        // globalAnalyzerMap[&ctxt]->dump();

        TranslationUnitDecl *UD = ctxt.getTranslationUnitDecl();
        AllStmtVisitor V(existing_stmts);
        V.TraverseDecl(UD);
        DeclContext *DC = UD;
        if (get_ext(file) == "cpp" || get_ext(file) == "cc") {
            LinkageSpecDecl *LSD = NULL;
            for (DeclContext::decl_iterator it = UD->decls_begin(); it != UD->decls_end(); ++it) {
                LSD = llvm::dyn_cast<LinkageSpecDecl>(*it);
                if (LSD) break;
            }
            if (LSD) DC = LSD;
        }

        for (DeclContext::decl_iterator it = DC->decls_begin(); it != DC->decls_end(); ++it) {
            FunctionDecl *FD = llvm::dyn_cast<FunctionDecl>(*it);
            if (FD && FD->getDeclName().isIdentifier()) {
                if (FD->getName() == IS_NEG_HANDLER)
                    internalHandlerMap[&ctxt].abstract_cond = createFExpr(ctxt, FD);
                if (FD->getName() == "memset")
                    internalHandlerMap[&ctxt].sys_memset = createFExpr(ctxt, FD);
                if (FD->getName() == UNKNOWN_HOOK)
                    internalHandlerMap[&ctxt].abstract_hole = createFExpr(ctxt, FD);
            }
        }
    }

    codeMap[file] = code;
}

std::string SourceContextManager::newSourceFile(const std::string &projDir, const std::string &srcFile,
        const std::string &buildDir, const std::vector<std::string> &buildArgs) {
    std::string key_srcfile = projDir + "/" + srcFile;
    std::string full_key_path = getFullPath(key_srcfile);
    assert( (codeMap.count(key_srcfile) == 0) && "Duplicate srcfile invoked!");
    std::string code;
    {
        DirectorySwitcher DS(projDir);
        readCodeToString(srcFile, code);
    }

    std::string prefix = "";
    if ((code.find("memset") == std::string::npos) && (code.find("string.h") == std::string::npos))
        prefix = std::string(HANDLER_PREFIX) + MEMSET_PREFIX;
    else
        prefix = std::string(HANDLER_PREFIX);
    if (get_ext(srcFile) == "cpp" || get_ext(srcFile) == "cc")
        prefix = "extern \"C\" { " + std::string(HANDLER_PREFIX) + "}";
    code = prefix + "\n" + code;

    codeMap[key_srcfile] = code;
    std::string target_dir = buildDir;
    if (target_dir == ".")
        target_dir = projDir;
    {
        DirectorySwitcher DS(target_dir);
        // We are going to include an implicit header lookup path of the current directory
        std::vector<std::string> tmpArgs;
        tmpArgs.clear();
        tmpArgs.push_back("-I");
        size_t idx = full_key_path.rfind("/");
        assert(idx != std::string::npos);
        tmpArgs.push_back(full_key_path.substr(0, idx));
        tmpArgs.insert(tmpArgs.end(), buildArgs.begin(), buildArgs.end());
        tmpArgs.push_back("-w");
        unitMap[key_srcfile] = tooling::buildASTFromCodeWithArgs(code, tmpArgs, key_srcfile);
    }
    std::unique_ptr<clang::ASTUnit> &unit = unitMap[key_srcfile];
    ASTContext &ctxt = unit->getASTContext();
    globalAnalyzerMap[&ctxt] = new GlobalAnalyzer(ctxt, key_srcfile);
    TranslationUnitDecl *UD = ctxt.getTranslationUnitDecl();
    AllStmtVisitor V(existing_stmts);
    V.TraverseDecl(UD);
    DeclContext *DC = UD;
    if (get_ext(srcFile) == "cpp" || get_ext(srcFile) == "cc") {
        LinkageSpecDecl *LSD = NULL;
        for (DeclContext::decl_iterator it = UD->decls_begin(); it != UD->decls_end(); ++it) {
            LSD = llvm::dyn_cast<LinkageSpecDecl>(*it);
            if (LSD) break;
        }
        if (LSD) DC = LSD;
    }

    for (DeclContext::decl_iterator it = DC->decls_begin(); it != DC->decls_end(); ++it) {
        FunctionDecl *FD = llvm::dyn_cast<FunctionDecl>(*it);
        if (FD && FD->getDeclName().isIdentifier()) {
            if (FD->getName() == IS_NEG_HANDLER)
                internalHandlerMap[&ctxt].abstract_cond = createFExpr(ctxt, FD);
            if (FD->getName() == "memset")
                internalHandlerMap[&ctxt].sys_memset = createFExpr(ctxt, FD);
            if (FD->getName() == UNKNOWN_HOOK)
                internalHandlerMap[&ctxt].abstract_hole = createFExpr(ctxt, FD);
        }
    }

    return key_srcfile;
}

/*void SourceContextManager::pushChanges(RepairCandidate &candidate) {
    StmtList.clear();
    CompoundStmt *CS = candidate.loc.parent_stmt;
    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it)
        StmtList.push_back(*it);
    candidate.loc.parent_stmt->setStmts(*getSourceContext(candidate.loc.filename),
            &candidate.stmts[0], candidate.stmts.size());
}

void SourceContextManager::popChanges(RepairCandidate &candidate) {
    candidate.loc.parent_stmt->setStmts(*getSourceContext(candidate.loc.filename),
            &StmtList[0], StmtList.size());
}*/

LocalAnalyzer* SourceContextManager::getLocalAnalyzer(const ASTLocTy &loc) {
    if (localAnalyzerMap.count(loc) == 0) {
        ASTContext *C = getSourceContext(loc.filename);
        //llvm::errs() << "Location " << loc.filename << ":" << getExpLineNumber(*C, loc.stmt) << "\n";
        //loc.stmt->printPretty(llvm::errs(), 0, C->getPrintingPolicy());
        localAnalyzerMap[loc] = new LocalAnalyzer(C, globalAnalyzerMap[C], loc, naive);
        //std::set<Expr*> exprs = localAnalyzerMap[loc]->getCandidateInsertExprs();
        //llvm::errs() << "Tot expr " << exprs.size() << "\n";
        //for (std::set<Expr*>::iterator it = exprs.begin(); it != exprs.end(); ++it) {
            //(*it)->printPretty(llvm::errs(), 0, C->getPrintingPolicy());
            //llvm::errs() << "\n";
        //}
        //std::set<Stmt*> stmts = localAnalyzerMap[loc]->getCandidateMacroExps();
        //llvm::errs() << "Tot macro " << stmts.size() << "\n";
        //for (std::set<Stmt*>::iterator it = stmts.begin(); it != stmts.end(); ++it) {
            //(*it)->printPretty(llvm::errs(), 0, C->getPrintingPolicy());
            //llvm::errs() << "\n";
        //}
    }
    return localAnalyzerMap[loc];
}

// FIXME: This stupid shit should go somewhere else
Expr* SourceContextManager::getExprPlaceholder(ASTContext *ctxt, clang::QualType QT) {
    Expr *abstract_cond = getInternalHandlerInfo(ctxt).abstract_cond;
    return new(*ctxt) CallExpr(*ctxt, abstract_cond, std::vector<Expr*>(),
            QT, VK_RValue, SourceLocation());
}

Expr* SourceContextManager::getUnknownExpr(ASTContext *ctxt, ExprListTy candidate_atoms) {
    Expr *abstract_hole = getInternalHandlerInfo(ctxt).abstract_hole;
    return new(*ctxt) CallExpr(*ctxt, abstract_hole, candidate_atoms,
        ctxt->IntTy, VK_RValue, SourceLocation());
}

std::string SourceContextManager::cleanUpCode(const std::string &code) {
    std::string ret = code;
    size_t idx = code.find("\n");
    assert( idx != std::string::npos);
    ret = ret.substr(idx + 1);
    if (ret.find("memset") != std::string::npos && ((ret.find("<string.h>") == std::string::npos) || (ret.find("ifdef") != std::string::npos)))
        ret = std::string("#include <string.h>\n") + ret;
    return ret;
}
