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
#include "llvm/Support/CommandLine.h"
#include "SourceContextManager.h"
#include "RepairCandidateGenerator.h"
#include "FeatureVector.h"
#include "FeatureParameter.h"
#include "ASTDiffer.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Tooling/Tooling.h"
#include "Utils.h"
#include "config.h"
#include <string>
#include <vector>
#include <fstream>

using namespace clang;

llvm::cl::opt<std::string> ProjDir1(llvm::cl::Positional, llvm::cl::desc("projdir1"),
        llvm::cl::value_desc("The first project directory!"), llvm::cl::Required);
llvm::cl::opt<std::string> SrcFile1(llvm::cl::Positional, llvm::cl::desc("srcfile1"),
        llvm::cl::value_desc("The first src file name!"), llvm::cl::Required);
llvm::cl::opt<std::string> ProjDir2(llvm::cl::Positional, llvm::cl::desc("projdir2"),
        llvm::cl::value_desc("The second project directory!"), llvm::cl::Required);
llvm::cl::opt<std::string> SrcFile2(llvm::cl::Positional, llvm::cl::desc("srcfile2"),
        llvm::cl::value_desc("The second src file name!"), llvm::cl::Required);
llvm::cl::opt<std::string> ArgFile1("argf", llvm::cl::desc("argfile"),
        llvm::cl::value_desc("The argument file"));
llvm::cl::opt<std::string> ArgFile2("argf2", llvm::cl::init(""), llvm::cl::desc("argfile2"),
        llvm::cl::value_desc("The argument file for the second source file!"));
llvm::cl::opt<bool> PrintCandidateVec("print-candidate-vector");
llvm::cl::opt<bool> PrintDiff("print-diff-only", llvm::cl::init(false));
llvm::cl::opt<bool> IgnoreBuildDir("ignore-build-dir", llvm::cl::init(false));
llvm::cl::opt<std::string> ExtractFeature("extract-feature", llvm::cl::init(""));

// debug options
llvm::cl::opt<bool> PrintMemsetOnly("print-memset-only", llvm::cl::init(false));
llvm::cl::opt<bool> PrintMatchKind("print-match-kind", llvm::cl::init(false));

std::vector<std::string> build_args1, build_args2;
std::string build_dir1, build_dir2;
std::string code1, code2;
std::string srcfile1, srcfile2;

namespace {

class ConditionVisitor : public RecursiveASTVisitor<ConditionVisitor> {
    ASTContext *ast;
    std::set<std::string> res;
public:
    ConditionVisitor(ASTContext *ast): ast(ast), res() { }

    virtual bool TraverseStmt(Stmt *S) {
        if (S == NULL)
            return true;
        if (llvm::isa<DeclRefExpr>(S)) {
            res.insert(stmtToString(*ast, S));
            return true;
        }
        else if (llvm::isa<MemberExpr>(S)) {
            res.insert(stmtToString(*ast, S));
            return true;
        }
        else
            return RecursiveASTVisitor<ConditionVisitor>::TraverseStmt(S);
    }

    std::set<std::string> getResult() {
        return res;
    }
};

class ConditionBreaker : public RecursiveASTVisitor<ConditionBreaker> {
    ASTContext *ast;
    std::map<std::string, Stmt*> res;
public:
    ConditionBreaker(ASTContext *ast) : ast(ast), res() { }

    virtual bool TraverseStmt(Stmt *stmt) {
        BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(stmt);
        bool go_down = false;
        if (BO)
            if ((BO->getOpcode() == BO_LAnd) || (BO->getOpcode() == BO_LOr))
                go_down = true;

        if (llvm::isa<ParenExpr>(stmt))
            go_down = true;

        if (go_down) {
            bool ret = true;
            if (BO) {
                ret &= TraverseStmt(BO->getLHS());
                ret &= TraverseStmt(BO->getRHS());
                return ret;
            }
            else {
                ret = RecursiveASTVisitor<ConditionBreaker>::TraverseStmt(stmt);
                return ret;
            }
        }
        else {
            if (stmt)
                res[stmtToString(*ast, stmt)] = stmt;
        }
        return true;
    }

    std::map<std::string, Stmt*> getResult() {
        return res;
    }
};

}

bool lookupCandidateAtoms(const RepairCandidate &rc, ASTContext *ast, const std::set<std::string> &expr_strs, std::set<Expr*> &res) {
    std::set<Expr*> atoms = rc.getCandidateAtoms();
    std::map<std::string, Expr*> tmp;
    tmp.clear();
    for (std::set<Expr*>::iterator it = atoms.begin(); it != atoms.end(); ++it) {
        tmp[stmtToString(*ast, *it)] = *it;
    }
    res.clear();
    for (std::set<std::string>::iterator it = expr_strs.begin(); it != expr_strs.end(); ++it)
        if (tmp.count(*it))
            res.insert(tmp[*it]);
    return true;
}

static std::string normalize(std::string str) {
    std::string tmps = str;
    size_t i = tmps.find("sizeof");
    if (i != std::string::npos) {
        while ((i < tmps.size()) && (tmps[i] != '('))
            i++;
        if (i < tmps.size()) {
            size_t j = i;
            int cnt = 0;
            while (j < tmps.size()) {
                if (tmps[j] == '(')
                    cnt ++;
                if (tmps[j] == ')') {
                    cnt --;
                    if (cnt == 0) break;
                }
                j++;
            }
            if (j < tmps.size()) {
                tmps = tmps.substr(0, i) + tmps.substr(j + 1);
            }
        }
    }
    str = tmps;
    tmps = "";
    for (size_t i = 0; i < str.size(); i++) {
        if (str[i] != '(' && str[i] != ')' && str[i] != ' ')
            tmps.push_back(str[i]);
        // XXX: This is shitty I want to remove *& from the string
        if (tmps.size() > 1)
            if ((tmps[tmps.size() - 1] == '&') && (tmps[tmps.size() - 2] == '*'))
                tmps.resize(tmps.size() - 2);
    }
    return tmps;
}

bool sameStmtByString(ASTContext *ast1, Stmt* S1, ASTContext *ast2, Stmt* S2) {
    std::string str1 = stmtToString(*ast1, S1);
    std::string str2 = stmtToString(*ast2, S2);
    // FIXME: I know this is hacky and may potentially cause false positive,
    // but whatever!
    std::string tmps1 = normalize(str1);
    std::string tmps2 = normalize(str2);
    /*llvm::errs() << "Match:\n";
    llvm::errs() << str1 << "\n";
    llvm::errs() << str2 << "\n";
    llvm::errs() << tmps1 << "\n";
    llvm::errs() << tmps2 << "\n";*/
    return tmps1 == tmps2;
}

static bool matchCandidateWithHumanFix(const RepairCandidate &rc, ASTDiffer &differ, std::set<clang::Expr*> &insMatchSet) {
    std::vector<DiffResultEntry> res;
    differ.GetDiffResultForStmt(res);
    if (res.size() != 1)
        return false;
    DiffResultEntry res0 = res[0];
    ASTContext *ast1 = differ.getAST1();
    ASTContext *ast2 = differ.getAST2();


    // replace string kind
    if (rc.kind == RepairCandidate::ReplaceStringKind)
        if (res0.DiffActionKind == ASTDiffer::ReplaceAction) {
            std::vector<DiffResultEntry> res_expr;
            differ.GetDiffResult(res_expr);
            if (res_expr.size() == 1) {
                StringLiteral *SL1 = llvm::dyn_cast<StringLiteral>(stripParenAndCast(rc.oldRExpr));
                Expr* tmpE = llvm::dyn_cast<Expr>(res_expr[0].Node1.stmt);
                if (tmpE) {
                    StringLiteral *SL2 = llvm::dyn_cast<StringLiteral>(stripParenAndCast(tmpE));
                    if (SL1 && SL2)
                        if (SL1 == SL2) {
                            insMatchSet.clear();
                            insMatchSet.insert(NULL);
                            return true;
                        }
                }
            }
        }

    // add special guard
    if (res0.DiffActionKind == ASTDiffer::ReplaceAction)
        if (res0.NodeKind2 == ASTDiffer::StmtKind) {
            IfStmt *IF1 = llvm::dyn_cast<IfStmt>(res0.Node1.stmt);
            IfStmt *IF2 = llvm::dyn_cast<IfStmt>(res0.Node2.stmt);
            if (IF1 && IF2) {
                BinaryOperator* condE = llvm::dyn_cast<BinaryOperator>(IF2->getCond());
                if (condE)
                    if (condE->getOpcode() == BO_LAnd)
                        if (sameStmtByString(ast1, IF1->getCond(), ast2, condE->getRHS())) {
                            if (rc.kind == RepairCandidate::SpecialGuardKind) {
                                ConditionVisitor CV(ast2);
                                CV.TraverseStmt(condE->getLHS());
                                std::set<std::string> vars2 = CV.getResult();
                                bool ret = lookupCandidateAtoms(rc, ast1, vars2, insMatchSet);
                                return ret;
                            }
                            else {
                                return false;
                            }
                        }
            }
        }

    // change a condition
    if (rc.kind == RepairCandidate::TightenConditionKind || rc.kind == RepairCandidate::LoosenConditionKind) {
        if (res0.DiffActionKind == ASTDiffer::ReplaceAction)
            if (res0.NodeKind1 == ASTDiffer::StmtKind && res0.NodeKind2 == ASTDiffer::StmtKind) {
                IfStmt *IF1 = llvm::dyn_cast<IfStmt>(res0.Node1.stmt);
                IfStmt *IF2 = llvm::dyn_cast<IfStmt>(res0.Node2.stmt);
                assert( rc.actions.size() > 0);
                IfStmt *locIF = llvm::dyn_cast<IfStmt>(rc.actions[0].loc.stmt);
                if (IF1 && IF2)
                    if (locIF == IF1)
                        if (sameStmtByString(ast1, IF1->getThen(), ast2, IF2->getThen()) &&
                            sameStmtByString(ast1, IF1->getElse(), ast2, IF2->getElse()))
                            if (differ.InSearchSpaceHelper()) {
                                Expr *Cond1 = IF1->getCond();
                                Expr *Cond2 = IF2->getCond();
                                // We first break two conditions with &&, || and () as sperator
                                std::map<std::string, Stmt*> varm1, varm2;
                                {
                                    ConditionBreaker CB(ast1);
                                    CB.TraverseStmt(Cond1);
                                    varm1 = CB.getResult();
                                }
                                {
                                    ConditionBreaker CB(ast2);
                                    CB.TraverseStmt(Cond2);
                                    varm2 = CB.getResult();
                                }
                                // Find out changed small clauses and get varaibles inside
                                std::set<std::string> tmp;
                                tmp.clear();
                                for (std::map<std::string, Stmt*>::iterator it = varm1.begin(); it != varm1.end(); it++)
                                    if (!varm2.count(it->first)) {
                                        ConditionVisitor CV(ast1);
                                        CV.TraverseStmt(it->second);
                                        std::set<std::string> vars1 = CV.getResult();
                                        tmp.insert(vars1.begin(), vars1.end());
                                    }
                                for (std::map<std::string, Stmt*>::iterator it = varm2.begin(); it != varm2.end(); it++)
                                    if (!varm1.count(it->first)) {
                                        ConditionVisitor CV(ast2);
                                        CV.TraverseStmt(it->second);
                                        std::set<std::string> vars2 = CV.getResult();
                                        tmp.insert(vars2.begin(), vars2.end());
                                    }
                                if (tmp.size() == 0) {
                                    // If we cannot find, we just assume it is operator changes, and we put NULL into the set
                                    insMatchSet.clear();
                                    insMatchSet.insert(NULL);
                                    return true;
                                }
                                else {
                                    bool ret = lookupCandidateAtoms(rc, ast1, tmp, insMatchSet);
                                    return ret;
                                }
                            }
            }
    }

    // add guard
    if (rc.kind == RepairCandidate::GuardKind) {
        if (res0.DiffActionKind == ASTDiffer::ReplaceAction) {
            if (res0.NodeKind1 == ASTDiffer::StmtKind && res0.NodeKind2 == ASTDiffer::StmtKind) {
                Stmt* S1 = res0.Node1.stmt;
                IfStmt* IF2 = llvm::dyn_cast<IfStmt>(res0.Node2.stmt);
                if (IF2) {
                    Stmt* ThenS = IF2->getThen();
                    // Avoid common single statement compound stmt
                    if (llvm::isa<CompoundStmt>(ThenS) && !llvm::isa<CompoundStmt>(S1)) {
                        CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ThenS);
                        if (CS->size() == 1)
                            ThenS = CS->body_back();
                    }
                    if (sameStmtByString(differ.getAST1(), S1, differ.getAST2(), ThenS) &&
                        (IF2->getElse() == NULL)) {
                        std::set<std::string> vars2;
                        ConditionVisitor CV(ast2);
                        CV.TraverseStmt(IF2->getCond());
                        vars2 = CV.getResult();
                        bool ret = lookupCandidateAtoms(rc, ast1, vars2, insMatchSet);
                        return ret;
                    }
                }
            }
        }
        else if (res0.DiffActionKind == ASTDiffer::DeleteAction) {
            insMatchSet = rc.getCandidateAtoms();
            return true;
        }
    }

    // add if-exit
    if (rc.kind == RepairCandidate::IfExitKind) {
        if (res0.DiffActionKind == ASTDiffer::InsertAction || res0.DiffActionKind == ASTDiffer::ReplaceAction) {
            //XXX: We specially handle the case where the repair replaces the return/goto statement
            bool yes = false;
            if (res0.DiffActionKind == ASTDiffer::ReplaceAction) {
                if ((res0.NodeKind1 == ASTDiffer::StmtKind) && (res0.NodeKind2 == ASTDiffer::StmtKind)) {
                    Stmt *S1 = res0.Node1.stmt;
                    Stmt *S2 = res0.Node2.stmt;
                    if ((llvm::isa<ReturnStmt>(S1) || llvm::isa<GotoStmt>(S1) || llvm::isa<BreakStmt>(S1)) &&
                        (llvm::isa<ReturnStmt>(S2) || llvm::isa<GotoStmt>(S2) || llvm::isa<BreakStmt>(S2)))
                        yes = true;
                }
            }
            else
                yes = true;

            if (yes)
                if (res0.NodeKind2 == ASTDiffer::StmtKind) {
                    // We have to dig make sure this
                    Stmt *S = res0.Node2.stmt;
                    IfStmt *IF2 = llvm::dyn_cast<IfStmt>(res0.Node2.stmt);
                    std::set<std::string> tmp;
                    tmp.clear();
                    if (IF2 && (IF2->getElse() == NULL)) {
                        S = IF2->getThen();
                        ConditionVisitor CV(ast2);
                        CV.TraverseStmt(IF2->getCond());
                        tmp = CV.getResult();
                    }
                    // Another tricky case is that S is wrapped by a compound statemt {}
                    // Sometimes human patch will have this dummy stuff
                    if (llvm::isa<CompoundStmt>(S)) {
                        CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(S);
                        if (CS->size() == 1)
                            S = CS->body_back();
                    }
                    assert(rc.actions.size() == 2);
                    assert(rc.actions[0].kind == RepairAction::InsertMutationKind);
                    IfStmt *rc_IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
                    assert( rc_IFS );
                    Stmt* rc_S = rc_IFS->getThen();
                    assert( rc_S );
                    if (llvm::isa<ReturnStmt>(S) || llvm::isa<GotoStmt>(S) || llvm::isa<BreakStmt>(S))
                        if (sameStmtByString(ast1, rc_S, ast2, S)) {
                            if (tmp.size() == 0) {
                                insMatchSet = rc.getCandidateAtoms();
                                return true;
                            }
                            else {
                                bool ret = lookupCandidateAtoms(rc, ast1, tmp, insMatchSet);
                                return ret;
                            }
                        }
                }
        }
    }

    // all rest of replace case
    if (rc.kind == RepairCandidate::ReplaceKind) {
        if (res0.DiffActionKind == ASTDiffer::ReplaceAction)
            if (res0.NodeKind2 == ASTDiffer::StmtKind) {
                assert(rc.actions.size() == 1);
                assert(rc.actions[0].kind == RepairAction::ReplaceMutationKind);
                Stmt *S1 = (Stmt*)rc.actions[0].ast_node;
                Stmt *S2 = res0.Node2.stmt;
                insMatchSet.clear();
                insMatchSet.insert(NULL);
                return sameStmtByString(ast1, S1, ast2, S2);
            }
    }
    if (rc.kind == RepairCandidate::AddInitKind || rc.kind == RepairCandidate::AddAndReplaceKind) {
        if (res0.DiffActionKind == ASTDiffer::InsertAction) {
            if (res0.NodeKind2 == ASTDiffer::StmtKind) {
                assert(rc.actions.size() == 1);
                assert(rc.actions[0].kind == RepairAction::InsertMutationKind);
                Stmt *S1 = (Stmt*)rc.actions[0].ast_node;
                Stmt *S2 = res0.Node2.stmt;
                insMatchSet.clear();
                insMatchSet.insert(NULL);
                return sameStmtByString(ast1, S1, ast2, S2);
            }
        }
    }
    return false;
}

std::vector<std::string> extraArgs() {
    // We need to put extra include directory arguments in to avoid compile error
    // when building AST trees
    std::string extra_paths = EXTRA_CLANG_INCLUDE_PATH;
    std::string tmp = "";
    std::vector<std::string> build_args;
    build_args.clear();
    for (size_t i = 0; i < extra_paths.size(); i++) {
        if (i != extra_paths.size() - 1)
            if ((extra_paths[i] == '-') && (extra_paths[i+1] == 'I')) {
                if (tmp != "") {
                    while (tmp.size() > 1)
                        if (tmp[tmp.size() -1] == ' ')
                            tmp.resize(tmp.size() - 1);
                        else
                            break;
                    build_args.push_back(tmp);
                }
                tmp = "";
            }
        if ((tmp != "") || extra_paths[i] != ' ')
            tmp.push_back(extra_paths[i]);
    }
    if (tmp != "") {
        while (tmp.size() > 1)
            if (tmp[tmp.size() -1] == ' ')
                tmp.resize(tmp.size() - 1);
            else
                break;
        build_args.push_back(tmp);
    }
    return build_args;
}

#define dumpNode(k, n) \
    do { \
        if ((k) == ASTDiffer::StmtKind)\
            (n).stmt->dump();\
        else\
            (n).decl->dump();\
    } \
    while(0)

namespace {

class MemsetVisitor : public RecursiveASTVisitor<MemsetVisitor> {
    bool res;
public:
    MemsetVisitor(): res(false) { }

    virtual bool VisitCallExpr(CallExpr *CE) {
        FunctionDecl *FD = CE->getDirectCallee();
        if (FD) {
            std::string fname = FD->getName();
            if (fname.find("memset") != std::string::npos)
                res = true;
        }
        return true;
    }

    bool getResult() {
        return res;
    }
};

class LocationFuzzer : public RecursiveASTVisitor<LocationFuzzer> {
    std::vector<Stmt*> stmtStack, parentStack;
    Stmt* loc;
public:
    LocationFuzzer(Stmt* loc): stmtStack(), parentStack(), loc(loc) { }

    bool TraverseStmt(Stmt *S) {
        stmtStack.push_back(S);
        if (S == loc)
            parentStack = stmtStack;
        bool ret = RecursiveASTVisitor::TraverseStmt(S);
        stmtStack.pop_back();
        return ret;
    }

    std::map<Stmt*, unsigned long> getResult() {
        assert( parentStack.size() > 1);
        assert( parentStack[parentStack.size() - 1] == loc);
        Stmt* parentS = parentStack[parentStack.size() - 2];
        CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(parentS);
        if (CS) {
            std::vector<Stmt*> v;
            int idx = -1;
            for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                if (*it == loc)
                    idx = v.size();
                v.push_back(*it);
            }
            assert( idx != -1);
            assert( v[idx] == loc);
            std::map<Stmt*, unsigned long> ret;
            ret.clear();
            if (idx != 0)
                ret[v[idx - 1]] = 0;
            ret[v[idx]] = 0;
            if ((size_t)idx != v.size() - 1)
                ret[v[idx + 1]] = 0;
            return ret;
        }
        else {
            std::map<Stmt*, unsigned long> ret;
            ret[parentS] = 0;
            ret[loc] = 0;
            return ret;
        }
    }
};

}

int main(int argc, char **argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv);
    if (ArgFile1.getValue() != "")
        parseArgFile(ArgFile1.getValue(), build_dir1, build_args1);
    else {
        build_dir1 = ".";
        build_args1 = extraArgs();
    }
    if (ArgFile2.getValue() != "")
        parseArgFile(ArgFile2.getValue(), build_dir2, build_args2);
    else {
        build_dir2 = build_dir1;
        build_args2 = build_args1;
    }

    if (IgnoreBuildDir.getValue()) {
        build_dir1 = ".";
        build_dir2 = ".";
    }

    SourceContextManager M;
    srcfile1 = M.newSourceFile(ProjDir1.getValue(), SrcFile1.getValue(), build_dir1, build_args1);
    srcfile2 = M.newSourceFile(ProjDir2.getValue(), SrcFile2.getValue(), build_dir2, build_args2);

    clang::ASTContext* ast1 = M.getSourceContext(srcfile1);
    clang::ASTContext* ast2 = M.getSourceContext(srcfile2);

    ASTDiffer differ(ast1, ast2);
    if (!differ.Diff()) {
        fprintf(stdout, "Differ failed!\n");
        return 2;
    }

    std::vector<DiffResultEntry> res;
    unsigned int distance = differ.GetDiffResultForStmt(res);
    bool print_diff = PrintDiff.getValue();
    std::string feature_file = ExtractFeature.getValue();

    bool print_memset = PrintMemsetOnly.getValue();
    if (print_memset) {
        if (res.size() != 1)
            return 1;
        if (res[0].DiffActionKind == ASTDiffer::InsertAction) {
            if (res[0].NodeKind2 == ASTDiffer::StmtKind) {
                MemsetVisitor MV;
                MV.TraverseStmt(res[0].Node2.stmt);
                if (MV.getResult()) {
                    res[0].Node2.stmt->dump();
                    return 0;
                }
            }
        }
        return 1;
    }

    if (print_diff) {
        llvm::errs() << "Distance " << distance << "\n";
        for (size_t i = 0; i < res.size(); i++) {
            llvm::outs() << "=========================\n";
            if (res[i].DiffActionKind == ASTDiffer::InsertAction) {
                llvm::errs() << "Insert:\n";
                dumpNode(res[i].NodeKind2, res[i].Node2);
                llvm::errs() << "At:\n";
                dumpNode(res[i].NodeKind1, res[i].Node1);
            }
            else if (res[i].DiffActionKind == ASTDiffer::DeleteAction) {
                llvm::errs() << "Delete:\n";
                dumpNode(res[i].NodeKind1, res[i].Node1);
            }
            else {
                llvm::errs() << "Replace:\n";
                dumpNode(res[i].NodeKind1, res[i].Node1);
                llvm::errs() << "With\n";
                dumpNode(res[i].NodeKind2, res[i].Node2);
            }
        }
        if (res.size() > 2) {
            llvm::errs() << "More than 2 statement!\n";
            return 1;
        }
        for (size_t i = 0; i < res.size(); i++)
            if (res[i].NodeKind1 != ASTDiffer::StmtKind || res[i].NodeKind2 != ASTDiffer::StmtKind) {
                llvm::errs() << "Not stmt type!\n";
                return 1;
            }
        return 0;
    }
    else {
        // FIXME: More patterns that handle more than 1 change needed
        if (res.size() == 0) {
            fprintf(stdout, "No AST difference!\n");
            return 1;
        }
        if (res.size() > 1) {
            fprintf(stdout, "Outside repair space!\n");
            return 1;
        }
        if (res[0].NodeKind1 != ASTDiffer::StmtKind) {
            fprintf(stdout, "Outside repair space!\n");
            return 1;
        }

        clang::Stmt* locStmt = (clang::Stmt*)res[0].Node1.stmt;
        if (locStmt && llvm::isa<NullStmt>(locStmt)) {
            fprintf(stdout, "Ignore null stmt!\n");
            return 1;
        }
        std::map<clang::Stmt*, unsigned long> locs;
        {
            LocationFuzzer Fuzz(locStmt);
            Fuzz.TraverseDecl(ast1->getTranslationUnitDecl());
            locs = Fuzz.getResult();
        }
        RepairCandidateGenerator G(M, srcfile1, locs, false, false);
        std::vector<RepairCandidate> spaces = G.run();
        bool found = false;
        std::ofstream f;
        if (feature_file != "") {
            llvm::outs() << "Total candidate: " << spaces.size() << "\n";
            f.open(feature_file.c_str(), std::ofstream::out);
        }
        FeatureExtractor EX;
        for (size_t i = 0; i < spaces.size(); i++) {
            //llvm::errs() << i << "\n";
            std::set<Expr*> insSet = spaces[i].getCandidateAtoms();
            std::set<Expr*> insMatchSet;
            assert( spaces[i].actions.size() > 0);
            bool res = false;
            if (spaces[i].actions[0].loc.stmt == locStmt)
                res = matchCandidateWithHumanFix(spaces[i], differ, insMatchSet);
            bool found_candidate = false;
            for (std::set<clang::Expr*>::iterator it =insSet.begin(); it != insSet.end(); it ++) {
                FeatureVector vec;
                if (feature_file != "" || PrintCandidateVec.getValue()) {
                    vec = EX.extractFeature(M, spaces[i], *it);
                }
                if (res && insMatchSet.count(*it)) {
                    vec.setMark();
                    if (!found_candidate) {
                        //llvm::outs() << "CandidateType: " << spaces[i].kind << "\n";
                        llvm::outs() << "Candidate:\n" << spaces[i].toString(M) << "\n";
                    }
                    found = true;
                    found_candidate = true;
                    llvm::outs() << "Found for:\n " << stmtToString(*ast1, *it) << "\n";
                    if (PrintCandidateVec.getValue())
                        vec.dump(llvm::outs());
                }
                if (f.is_open())
                    f << vec;
            }
        }
        if (feature_file != "")
            f.close();
        if (!found) {
            fprintf(stdout, "No Match Found!\n");
            return 1;
        }
    }

    return 0;
}
