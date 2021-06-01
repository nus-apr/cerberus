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
#include "GlobalAnalyzer.h"
#include "SourceContextManager.h"
#include "Utils.h"
#include "ASTUtils.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/RecursiveASTVisitor.h>

using namespace clang;

namespace {

class CandidateExprFinder : public RecursiveASTVisitor<CandidateExprFinder> {
    ASTContext &C;
    std::set<Expr*> &expr_set;
    std::set<Stmt*> &macro_set;
    std::set<Stmt*> &ifstmt_set;
    bool in_macro;

    // break a=b=c=0
    Expr* breakAssignChain(BinaryOperator *BO, std::vector<BinaryOperator*> &exprs) {
        Expr* RHS = BO->getRHS();
        BinaryOperator *RBO = llvm::dyn_cast<BinaryOperator>(RHS);
        if (!RBO || (RBO->getOpcode() != BO_Assign)) {
            exprs.push_back(BO);
            return RHS;
        }
        Expr* V = breakAssignChain(RBO, exprs);
        BinaryOperator *newBO = new(C) BinaryOperator(BO->getLHS(), V, BO_Assign, BO->getType(), VK_LValue, OK_Ordinary, SourceLocation(), false);
        exprs.push_back(newBO);
        return V;
    }

    void check(Expr* E) {
        if (llvm::isa<CallExpr>(E)) {
            expr_set.insert(E);
            return;
        }
        if (!in_macro) {
            if (llvm::isa<BinaryOperator>(E)) {
                BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(E);
                if (BO->getOpcode() == BO_Assign) {
                    // If this is a a=b=c=0, we are going to break it down
                    std::vector<BinaryOperator*> exprs;
                    exprs.clear();
                    breakAssignChain(BO, exprs);
                    for (size_t i = 0; i < exprs.size(); ++i)
                        expr_set.insert(exprs[i]);
                    return;
                }
            }
            else
                expr_set.insert(E);
        }
    }

    bool checkSimple(Stmt *S) {
        if (!S) return true;
        CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(S);
        if (CS) {
            for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it)
                if (!llvm::isa<ReturnStmt>(*it) && !llvm::isa<Expr>(*it))
                    return false;
            return true;
        }
        else
            return llvm::isa<ReturnStmt>(S) || llvm::isa<Expr>(S);
    }

public:
    CandidateExprFinder(ASTContext &C, std::set<Expr*> &expr_set, std::set<Stmt*> &macro_set,
            std::set<Stmt*> &ifstmt_set):
    C(C), expr_set(expr_set), macro_set(macro_set), ifstmt_set(ifstmt_set) {
        expr_set.clear();
        macro_set.clear();
        ifstmt_set.clear();
        in_macro = false;
    }

    virtual bool VisitIfStmt(IfStmt *IF) {
        Expr *thenE = llvm::dyn_cast<Expr>(IF->getThen());
        if (thenE) check(thenE);
        if (IF->getElse() != 0) {
            Expr *elseE = llvm::dyn_cast<Expr>(IF->getElse());
            if (elseE) check(elseE);
        }
        // We are going to include IfStmt if it includes only
        // simple assign/call/return
        if (!checkSimple(IF->getThen())) return true;
        if (!checkSimple(IF->getElse())) return true;
        ifstmt_set.insert(IF);
        return true;
    }

    virtual bool VisitForStmt(ForStmt *FS) {
        Expr *bodyE = llvm::dyn_cast<Expr>(FS->getBody());
        if (bodyE) check(bodyE);
        return true;
    }

    virtual bool TraverseCompoundStmt(CompoundStmt *CS) {
        // Test whether this is a macro
        SourceManager &M = C.getSourceManager();
        SourceLocation startLoc = CS->getLBracLoc();
        SourceLocation endLoc = CS->getRBracLoc();
        std::string filename = M.getFilename(M.getExpansionLoc(startLoc));
        //if (is_header(filename))
        //    return true;
        bool old_in_macro = in_macro;
        if (!in_macro && M.getExpansionLoc(startLoc) == M.getExpansionLoc(endLoc)) {
            macro_set.insert(CS);
            in_macro = true;
        }

        for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
            Expr *E = llvm::dyn_cast<Expr>(*it);
            /*llvm::errs() << "Processing:\n";
            E->dump();
            llvm::errs() << "in file: " << M.getFilename(M.getExpansionLoc(startLoc)) << "\n";*/
            if (E) check(E);
        }

        bool ret =  RecursiveASTVisitor::TraverseCompoundStmt(CS);
        in_macro = old_in_macro;
        return ret;
    }

    virtual bool TraverseDoStmt(DoStmt *DS) {
        // Do while is another possible macro definition
        SourceManager &M = C.getSourceManager();
        SourceLocation startLoc = DS->getLocStart();
        SourceLocation endLoc = DS->getLocEnd();
        std::string filename = M.getFilename(M.getExpansionLoc(startLoc));
        //if (is_header(filename))
        //    return true;
        if (M.getExpansionLoc(startLoc) == M.getExpansionLoc(endLoc)) {
            macro_set.insert(DS);
            return true;
        }
        else
            return RecursiveASTVisitor::TraverseDoStmt(DS);
    }

    /*
    virtual bool TraverseFunctionDecl(FunctionDecl *FD) {
        SourceManager &M = C.getSourceManager();
        SourceLocation startLoc = FD->getLocation();
        SourceLocation expLoc = M.getExpansionLoc(startLoc);
        std::string filename = M.getFilename(expLoc);
        if (!is_header(filename)) {
            return RecursiveASTVisitor::TraverseFunctionDecl(FD);
        }
        else {
            return true;
        }
    }
    */
};

class EnumDeclVisitor : public RecursiveASTVisitor<EnumDeclVisitor> {
    std::map<clang::EnumConstantDecl*, clang::EnumDecl*> &M;
public:
    EnumDeclVisitor(std::map<clang::EnumConstantDecl*, clang::EnumDecl*> &M): M(M) { }

    virtual bool VisitEnumDecl(EnumDecl *ED) {
        for (EnumDecl::decl_iterator it = ED->decls_begin(); it != ED->decls_end(); ++it) {
            EnumConstantDecl *ECD = llvm::dyn_cast<EnumConstantDecl>(*it);
            assert(ECD);
            M.insert(std::make_pair(ECD, ED));
        }
        return true;
    }
};

}

GlobalAnalyzer::GlobalAnalyzer(ASTContext &C, const std::string &filename): C(C), filename(filename) {
    CandidateExprs.clear();
    CandidateMacroExps.clear();
    CandidateIfStmts.clear();
    CandidateExprFinder V(C, CandidateExprs, CandidateMacroExps, CandidateIfStmts);
    V.TraverseDecl(C.getTranslationUnitDecl());

    GlobalVarDecls.clear();
    FuncDecls.clear();
    TranslationUnitDecl *TransUnit = C.getTranslationUnitDecl();
    for (DeclContext::decl_iterator it = TransUnit->decls_begin(); it != TransUnit->decls_end(); ++it) {
        VarDecl *VD = llvm::dyn_cast<VarDecl>(*it);
        if (VD) {
            SourceLocation src_loc = VD->getLocation();
            SourceManager &manager = C.getSourceManager();
            SourceLocation exp_loc = manager.getExpansionLoc(src_loc);
            if (!isSystemHeader(manager.getFilename(exp_loc))) {
               //VD->dump();
               GlobalVarDecls.insert(VD);
            }
        }
        FunctionDecl *FD = llvm::dyn_cast<FunctionDecl>(*it);
        if (FD && FD->getDeclName().isIdentifier() && (FD->getName() != IS_NEG_HANDLER) && (FD->getName() != UNKNOWN_HOOK))
            FuncDecls.insert(FD);
    }

    EnumMap.clear();
    EnumDeclVisitor V2(EnumMap);
    V2.TraverseDecl(C.getTranslationUnitDecl());
}

void GlobalAnalyzer::dump(bool pretty) {
    llvm::errs() << "Candidate Exprs: Tot " << CandidateExprs.size() << "\n";
    for (std::set<Expr*>::iterator it = CandidateExprs.begin(); it != CandidateExprs.end(); ++it) {
        Expr *E = *it;
        if (pretty) {
            llvm::errs() << stmtToString(C, E) << "\n";
        }
        else
            E->dump();
    }
    llvm::errs() << "Candidate MacroExp: Tot " << CandidateMacroExps.size() << "\n";
    for (std::set<Stmt*>::iterator it = CandidateMacroExps.begin(); it != CandidateMacroExps.end(); ++it) {
        Stmt *S = *it;
        if (pretty) {
            llvm::errs() << stmtToString(C, S) << "\n";
        }
        else
            S->dump();
    }
}

GlobalAnalyzer::ExprListTy GlobalAnalyzer::getCandidateEnumConstant(EnumConstantDecl *ECD) {
    ExprListTy ret;
    ret.clear();
    assert(EnumMap.count(ECD));
    EnumDecl *ED = EnumMap[ECD];
    for (EnumDecl::decl_iterator it = ED->decls_begin(); it != ED->decls_end(); ++it) {
        EnumConstantDecl *D = llvm::dyn_cast<EnumConstantDecl>(*it);
        assert(D);
        DeclRefExpr *DRE = DeclRefExpr::Create(C, NestedNameSpecifierLoc(),
                SourceLocation(), D, false, SourceLocation(), D->getType(), VK_RValue);
        ret.push_back(DRE);
    }
    return ret;
}
