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
#pragma once
#include "ASTUtils.h"
#include <vector>
#include <map>
#include <set>
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ASTContext.h"
#include "GlobalAnalyzer.h"

class GlobalAnalyzer;

class LocalAnalyzer {
    typedef std::vector<clang::Stmt*> StmtStackTy;
    typedef std::vector<clang::Expr*> ExprListTy;
    clang::ASTContext *ctxt;
    ASTLocTy loc;
    GlobalAnalyzer *G;
    clang::FunctionDecl *curFunc;
    std::set<clang::VarDecl*> LocalVarDecls;
    std::set<long long> IntegerConstants;
    std::set<clang::Expr*> MemberStems;
    std::map<std::string, std::set<size_t> > ExprDis;
    std::vector<clang::LabelDecl*> LocalLabels;
    bool inside_loop;
    bool naive;

    /*
    struct SynResTy {
        size_t idx;
        long long v;
        size_t flag;
        SynResTy(): idx(), v(), flag() {}

        SynResTy(size_t idx, long long v, size_t flag):
            idx(idx), v(v), flag(flag) {}

        bool operator < (const SynResTy &a) const {
            if (idx != a.idx)
                return idx < a.idx;
            else if (v != a.v)
                return v < a.v;
            else
                return flag < a.flag;
        }
    };
    */

    //SynResTy last_res;
    //std::set<SynResTy> disabled_res;

public:
    LocalAnalyzer(clang::ASTContext *ctxt, GlobalAnalyzer* G, ASTLocTy loc, bool naive);

    ~LocalAnalyzer() { }

    clang::Expr* castToRValue(clang::Expr* lvalue) {
        clang::ImplicitCastExpr *ICE = clang::ImplicitCastExpr::Create(*ctxt, lvalue->getType(),
                clang::CK_LValueToRValue, lvalue, 0, clang::VK_RValue);
        return ICE;
    }

    ExprListTy genExprAtoms(clang::QualType QT, bool allow_local = true, bool allow_glob = true, bool allow_field = true, bool allow_const = true, bool lvalue = false);

    bool isInsideLoop() {
        return inside_loop;
    }

    clang::FunctionDecl* getCurrentFunction() {
        return curFunc;
    }

    ExprListTy getCandidateExprsInType(clang::QualType QT) {
        return genExprAtoms(QT);
    }

    ExprListTy getCandidateConstantInType(clang::QualType QT) {
        return genExprAtoms(QT, false, false, false, true);
    }

    ExprListTy getCandidateLValueExpr() {
        return genExprAtoms(clang::QualType(), true, true, true, false, true);
    }

    ExprListTy getCandidateReturnExpr() {
        return genExprAtoms(curFunc->getCallResultType(), false, false, false, true);
    }

    ExprListTy getCandidateExpr() {
        return genExprAtoms(clang::QualType(), true, true, true, false);
    }

    ExprListTy getCandidateCalleeFunction(clang::CallExpr *CE, bool result_not_used);

    ExprListTy getCandidatePointerForMemset(size_t max_dis);

    size_t getExprDistance(clang::Expr *E, size_t line_number);

    size_t getExprDistance(clang::Expr *E, clang::Stmt* S);

    const std::set<clang::VarDecl*> &getLocalVarDecls() {
        return LocalVarDecls;
    }

    const std::set<clang::VarDecl*> &getGlobalVarDecls() {
        return G->getGlobalVarDecls();
    }

    std::set<clang::Expr*> getCandidateInsertExprs();

    std::set<clang::Expr*> getGlobalCandidateExprs();

    std::set<clang::Stmt*> getGlobalCandidateIfStmts();

    std::set<clang::Stmt*> getCandidateMacroExps();

    bool isValidStmt(clang::Stmt* S, clang::Expr** invalidSubExpr);

    ExprListTy getCandidateEnumConstant(clang::EnumConstantDecl *ECD);

    ExprListTy getCandidateLocalVars(clang::QualType QT) {
        return genExprAtoms(QT, true, false, false, false, false);
    }

    //clang::CallExpr* getIsNegCall(clang::Expr* is_neg_fn, size_t line_number);

    ExprListTy getCondCandidateVars(clang::SourceLocation SL);

/*    clang::Expr* synthesizeResult(ExprListTy exps,
            const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
            const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
            const std::set<unsigned long> &negative_cases,
            const std::set<unsigned long> &positive_cases);

    void lastSynthesizeFailed();

    void clearSynthesizeCache() {
        disabled_res.clear();
    }*/

    std::vector<clang::LabelDecl*> getCandidateGotoLabels() {
        return LocalLabels;
    }
};

