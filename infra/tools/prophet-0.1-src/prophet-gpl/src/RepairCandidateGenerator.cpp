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
#include "ASTUtils.h"
#include "RepairCandidateGenerator.h"
#include "LocalAnalyzer.h"
#include "CodeRewrite.h"
#include "llvm/Support/CommandLine.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <queue>
#include <math.h>

//#define DISABLE_IFSTMT_INSERT

using namespace clang;

llvm::cl::opt<bool> ReplaceExt("replace-ext", llvm::cl::init(false),
        llvm::cl::desc("Replace extension"));

#define PRIORITY_ALPHA 5000

namespace {

class AtomReplaceVisitor : public RecursiveASTVisitor<AtomReplaceVisitor> {
    LocalAnalyzer *L;
    ASTContext *ctxt;
    Stmt* start_stmt;
    std::set<clang::Stmt*> res;
    std::map<clang::Stmt*, std::pair<Expr*, Expr*> > resRExpr;
    bool replace_ext;

    ExprListTy secondOrderExprs(LocalAnalyzer *L, QualType QT) {
        ExprListTy ret;
        ret.clear();
        ExprListTy vars = L->getCandidateLocalVars(clang::QualType());
        const BinaryOperatorKind op_kind[5] = {BO_Add, BO_Sub, BO_Mul, BO_EQ, BO_NE};
        for (size_t i = 0; i < vars.size(); i++) {
            Expr* Ei = vars[i];
            if (QT->isIntegerType()) {
                for (size_t j = 0; j < vars.size(); j++) {
                    if (i == j) continue;
                    Expr* Ej = vars[j];
                    if (!Ei->getType()->isIntegerType() &&
                            !Ei->getType()->isPointerType())
                        continue;
                    if (Ei->getType()->isIntegerType() !=
                            Ej->getType()->isIntegerType())
                        continue;
                    if (Ei->getType()->isPointerType() !=
                            Ej->getType()->isPointerType())
                        continue;
                    if (Ei->getType()->isPointerType())
                        if (!typeMatch(Ei->getType(), Ej->getType()))
                            continue;
                    for (size_t k = 0; k < 5; k++) {
                        if (i > j)
                            if (k != 2)
                                continue;
                        if ((k < 3) && (!Ei->getType()->isIntegerType()))
                            continue;
                        //FIXME: Maybe this does not type check!
                        BinaryOperator *BO = new(*ctxt)
                            BinaryOperator(Ei, Ej, op_kind[k], Ei->getType(),
                            VK_RValue, OK_Ordinary, SourceLocation(), false);
                        ret.push_back(BO);
                    }
                }
                for (size_t k = 0; k < 5; k++) {
                    BinaryOperator *BO;
                    if ((k < 3) && (!Ei->getType()->isIntegerType()))
                        continue;
                    if (k == 2)
                        BO = new(*ctxt)
                        BinaryOperator(getNewIntegerLiteral(ctxt, 0), Ei, op_kind[k], Ei->getType(),
                        VK_RValue, OK_Ordinary, SourceLocation(), false);
                    else {
                        BO = new(*ctxt)
                        BinaryOperator(Ei, getNewIntegerLiteral(ctxt, 0), op_kind[k], Ei->getType(),
                        VK_RValue, OK_Ordinary, SourceLocation(), false);
                    }
                    ret.push_back(BO);
                }
            }
            if (QT->isPointerType() || QT->isArrayType()) {
                UnaryOperator *UO = new(*ctxt) UnaryOperator(Ei,
                    UO_AddrOf, ctxt->getPointerType(Ei->getType()),
                    VK_RValue, OK_Ordinary, SourceLocation());
                ret.push_back(UO);
            }
        }
        return ret;
    }

public:
    AtomReplaceVisitor(ASTContext *ctxt, LocalAnalyzer *L, clang::Stmt *start_stmt, bool replace_ext):
    L(L), ctxt(ctxt), start_stmt(start_stmt), res(), resRExpr(), replace_ext(replace_ext) {
        res.clear(); resRExpr.clear();
    }

    virtual bool VisitIntegerLiteral(IntegerLiteral *IL) {
        if (replace_ext) {
            ExprListTy exprs;
            exprs.clear();
            exprs.push_back(getNewIntegerLiteral(ctxt, 0));
            ExprListTy tmp = secondOrderExprs(L, IL->getType());
            exprs.insert(exprs.end(), tmp.begin(), tmp.end());
            for (size_t i = 0; i < exprs.size(); i++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(IL, newE);
                Stmt* S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(IL, newE);
            }
        }
        return true;
    }

    virtual bool VisitStringLiteral(StringLiteral *SL) {
        if (replace_ext) {
            ExprListTy exprs;
            exprs.clear();
            exprs.push_back(getNewIntegerLiteral(ctxt, 0));
            ExprListTy tmp = secondOrderExprs(L, SL->getType());
            exprs.insert(exprs.end(), tmp.begin(), tmp.end());
            for (size_t i = 0; i < exprs.size(); i++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(SL, newE);
                Stmt* S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(SL, newE);
            }
        }
        return true;
    }

    virtual bool VisitDeclRefExpr(DeclRefExpr *DRE) {
        ValueDecl *VD = DRE->getDecl();
        // If this is a Enumerate, we are going to replace with other type
        if (llvm::isa<EnumConstantDecl>(VD)) {
            EnumConstantDecl *ECD = llvm::dyn_cast<EnumConstantDecl>(VD);
            ExprListTy exprs = L->getCandidateEnumConstant(ECD);
            if (replace_ext) {
                ExprListTy tmp = secondOrderExprs(L, VD->getType());
                exprs.insert(exprs.end(), tmp.begin(), tmp.end());
            }
            for (size_t i = 0; i < exprs.size(); i ++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(DRE, newE);
                Stmt* S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(DRE, newE);
            }
        }
        // If this is a vardecl with pointer type, we are going to replace it with
        // other choice
        if (llvm::isa<VarDecl>(VD)) {
            QualType QT = DRE->getType();
            if (QT->isPointerType() || replace_ext) {
                ExprListTy exprs = L->getCandidateLocalVars(QT);
                if (replace_ext) {
                    ExprListTy tmp = secondOrderExprs(L, VD->getType());
                    exprs.insert(exprs.end(), tmp.begin(), tmp.end());
                }
                if (exprs.size() != 0) {
                    for (size_t i = 0; i < exprs.size(); i++) {
                        StmtReplacer R(ctxt, start_stmt);
                        Expr *newE = getParenExpr(ctxt, exprs[i]);
                        R.addRule(DRE, newE);
                        Stmt *S = R.getResult();
                        res.insert(S);
                        resRExpr[S] = std::make_pair(DRE, newE);
                    }
                }
            }
        }
        return true;
    }

    // I want to replace (- integer) as a whole
    virtual bool TraverseUnaryMinus(UnaryOperator *UO) {
        Expr* sub = UO->getSubExpr();
        if (isIntegerConstant(sub)) {
            if (replace_ext) {
                ExprListTy exprs;
                exprs.clear();
                exprs.push_back(getNewIntegerLiteral(ctxt, 0));
                ExprListTy tmp = secondOrderExprs(L, UO->getType());
                exprs.insert(exprs.end(), tmp.begin(), tmp.end());
                for (size_t i = 0; i < exprs.size(); i++) {
                    StmtReplacer R(ctxt, start_stmt);
                    Expr *newE = getParenExpr(ctxt, exprs[i]);
                    R.addRule(UO, newE);
                    Stmt* S = R.getResult();
                    res.insert(S);
                    resRExpr[S] = std::make_pair(UO, newE);
                }
            }
            return true;
        }
        else {
            return RecursiveASTVisitor::TraverseUnaryOperator(UO);
        }
    }

    virtual bool TraverseBinAssign(BinaryOperator *n) {
        Expr* RHS = n->getRHS();
        if (isIntegerConstant(RHS)) {
            ExprListTy exprs = L->getCandidateConstantInType(RHS->getType());
            for (size_t i = 0; i < exprs.size(); i++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(RHS, newE);
                Stmt *S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(RHS, newE);
            }
        }
        QualType QT = RHS->getType();
        ExprListTy exprs = L->getCandidateLocalVars(QT);
        if (exprs.size() != 0) {
            for (size_t i = 0; i < exprs.size(); i++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(RHS, newE);
                Stmt *S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(RHS, newE);
            }
        }
        if (QT->isIntegerType()) {
            exprs = L->getCandidateConstantInType(QT);
            for (size_t i = 0; i < exprs.size(); i++) {
                StmtReplacer R(ctxt, start_stmt);
                Expr *newE = getParenExpr(ctxt, exprs[i]);
                R.addRule(RHS, newE);
                Stmt *S = R.getResult();
                res.insert(S);
                resRExpr[S] = std::make_pair(RHS, newE);
            }
        }
        return TraverseStmt(RHS);
    }

    virtual std::set<Stmt*> getResult() {
        return res;
    }

    Expr* getOldRExpr(Stmt *S) {
        return resRExpr[S].first;
    }

    Expr* getNewRExpr(Stmt *S) {
        return resRExpr[S].second;
    }
};

class StringConstReplaceVisitor : public RecursiveASTVisitor<StringConstReplaceVisitor> {
    SourceContextManager &M;
    ASTContext *ctxt;
    Stmt* start_stmt;
    std::set<std::pair<Stmt*, Expr*> > res;
    std::map<Stmt*, Expr*> oldRExpr;
public:
    StringConstReplaceVisitor(SourceContextManager &M, ASTContext *ctxt, Stmt* start_stmt):
        M(M), ctxt(ctxt), start_stmt(start_stmt), res(), oldRExpr() { }

    virtual bool TraverseImplicitCastExpr(ImplicitCastExpr *ICE) {
        const QualType ConstCharP = ctxt->getPointerType(ctxt->getConstType(ctxt->CharTy));
        /*llvm::errs() << "checking:\n";
        ICE->dump();
        start_stmt->dump();
        ICE->getType()->dump();
        ConstCharP->dump();*/
        if (ctxt->hasSameType(ICE->getType(), ConstCharP)) {
            Expr *E1 = stripParenAndCast(ICE);
            if (llvm::isa<StringLiteral>(E1)) {
                Expr *placeholder = M.getExprPlaceholder(ctxt, ConstCharP);
                StmtReplacer R(ctxt, start_stmt);
                R.addRule(ICE, placeholder);
                Stmt *S = R.getResult();
                res.insert(std::make_pair(S, placeholder));
                oldRExpr[S] = ICE;
                return true;
            }
        }
        return RecursiveASTVisitor::TraverseImplicitCastExpr(ICE);
    }

    std::set<std::pair<Stmt*, Expr*> > getResult() {
        return res;
    }

    Expr* getOldRExpr(Stmt* S) {
        return oldRExpr[S];
    }
};

class CallExprReplaceVisitor : public RecursiveASTVisitor<CallExprReplaceVisitor> {
    LocalAnalyzer *L;
    ASTContext *ctxt;
    Stmt* start_stmt;
    std::vector<Stmt*> res;
    std::map<clang::Stmt*, std::pair<Expr*, Expr*> > resRExpr;
public:
    CallExprReplaceVisitor(ASTContext *ctxt, LocalAnalyzer *L, Stmt* start_stmt):
        L(L), ctxt(ctxt), start_stmt(start_stmt), res(), resRExpr() {
            res.clear();
            resRExpr.clear();
        }

    virtual bool VisitCallExpr(CallExpr *n) {
        // change the callee of a function call
        Expr *callee = n->getCallee();
        ExprListTy tmp = L->getCandidateCalleeFunction(n, n == start_stmt);
        for (size_t i = 0; i < tmp.size(); i++) {
            StmtReplacer R(ctxt, start_stmt);
            R.addRule(callee, tmp[i]);
            Stmt *S = R.getResult();
            res.push_back(S);
            resRExpr[S] = std::make_pair(callee, tmp[i]);
        }
        return true;
    }

    virtual std::vector<Stmt*> getResult() {
        return res;
    }

    Expr* getOldRExpr(Stmt *S) {
        return resRExpr[S].first;
    }

    Expr* getNewRExpr(Stmt *S) {
        return resRExpr[S].second;
    }
};

ASTLocTy newStatementLoc(const ASTLocTy &loc, Stmt *n) {
    ASTLocTy ret = loc;
    ret.stmt = n;
    return ret;
}

/*ASTLocTy newStatementLoc(const ASTLocTy &loc, Stmt *parent_stmt, Stmt *n) {
    ASTLocTy ret = loc;
    ret.parent_stmt = parent_stmt;
    ret.stmt = n;
    return ret;
}*/

IfStmt* duplicateIfStmt(ASTContext *ctxt, IfStmt *IS, Expr* new_cond) {
    IfStmt *ret = new(*ctxt) IfStmt(*ctxt, SourceLocation(), IS->getConditionVariable(),
            new_cond, IS->getThen(), SourceLocation(), IS->getElse());
    return ret;
}

class CallVisitor : public RecursiveASTVisitor<CallVisitor> {
    bool found;
public:
    CallVisitor() : found(false) { }

    bool VisitCallExpr(CallExpr *CE) {
        found = true;
        return true;
    }

    bool getResult() {
        return found;
    }
};

bool hasCallExpr(Stmt *S) {
    CallVisitor V;
    V.TraverseStmt(S);
    return V.getResult();
}

}

class RepairCandidateGeneratorImpl : public RecursiveASTVisitor<RepairCandidateGeneratorImpl> {
    ASTContext *ctxt;
    SourceContextManager &M;
    std::string file;
    std::vector<RepairCandidate> q;
    const std::map<Stmt*, unsigned long> &loc_map;
    std::map<Stmt*, unsigned long> loc_map1;
    std::map<CompoundStmt*, size_t> compound_counter;
    std::vector<Stmt*> stmt_stack;
    InternalHandlerInfo hinfo;
    // This is a hacky tmp list for fix is_first + is_func_block
    std::vector<size_t> tmp_memo;
    bool naive;
    bool learning;
    bool in_yacc_func;
    bool in_float;
    double GeoP;

    bool isTainted(Stmt *S) {
        if (S == NULL) return false;
        if (loc_map.count(S) != 0)
            return true;
        CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(S);
        if (!CS) return false;
        return compound_counter[CS] >= 2 || (compound_counter[CS] == CS->size() && CS->size() >= 1);
    }

    ASTLocTy getNowLocation(Stmt *n) {
        assert( stmt_stack.size() > 1 );
        Stmt *parent_stmt = stmt_stack[stmt_stack.size() - 2];
        SourceManager &M = ctxt->getSourceManager();
        SourceLocation exp_loc = M.getExpansionLoc(n->getLocStart());
        std::string src_file = M.getFilename(exp_loc);
        return ASTLocTy(file, src_file, parent_stmt, n);
    }

    double getPriority(Stmt *n) {
        // temporary
        assert( loc_map1.count(n) > 0);
        return -((double)loc_map1[n]);
        /*std::map<Stmt*, size_t>::const_iterator it = loc_map.find(n);
        if (it == loc_map.end())
            return 0;
        else
            return -((double)it->second);*/
    }

    double getLocScore(Stmt *n) {
        assert( loc_map1.count(n) > 0);
        double score = log(1-GeoP) * loc_map1[n] + log(GeoP);
        if (llvm::isa<LabelStmt>(n))
            score += 4.5;
        return score;
    }

    // The set of mutation generation subroutines
    void genTightCondition(IfStmt *n) {
        if (in_yacc_func) return;
        Expr *ori_cond = n->getCond();
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        //assert(ori_cond->getType()->isIntegerType());
        Expr *placeholder;
        if (naive)
            placeholder = getNewIntegerLiteral(ctxt, 1);
        else
            placeholder = M.getExprPlaceholder(ctxt, ctxt->IntTy);
        UnaryOperator *UO = new(*ctxt) UnaryOperator(placeholder,
                UO_LNot, ori_cond->getType(), VK_RValue, OK_Ordinary, SourceLocation());
        ParenExpr *ParenE = new(*ctxt) ParenExpr(SourceLocation(), SourceLocation(), ori_cond);
        BinaryOperator *BO = new(*ctxt) BinaryOperator(ParenE, UO, BO_LAnd, ctxt->IntTy,
                VK_RValue, OK_Ordinary, SourceLocation(), false);
        IfStmt *S = duplicateIfStmt(ctxt, n, BO);
        RepairCandidate rc;
        rc.actions.clear();
        rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, S));
        if (!naive) {
            ExprListTy candidateVars = L->getCondCandidateVars(ori_cond->getLocEnd());
            rc.actions.push_back(RepairAction(newStatementLoc(loc, S), placeholder,
                        candidateVars));
        }
        // FIXME: priority!
        if (learning)
            rc.score = getLocScore(n);
        else
            rc.score = 4*PRIORITY_ALPHA;
        rc.kind = RepairCandidate::TightenConditionKind;
        q.push_back(rc);
    }

    void genLooseCondition(IfStmt *n) {
        if (in_yacc_func) return;
        Expr *ori_cond = n->getCond();
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        //assert(ori_cond->getType()->isIntegerType());
        ParenExpr *ParenE = new(*ctxt) ParenExpr(SourceLocation(), SourceLocation(), ori_cond);
        Expr* placeholder;
        if (naive)
            placeholder = getNewIntegerLiteral(ctxt, 1);
        else
            placeholder = M.getExprPlaceholder(ctxt, ctxt->IntTy);
        BinaryOperator *BO = new(*ctxt) BinaryOperator(ParenE,
                placeholder, BO_LOr, ctxt->IntTy, VK_RValue,
                OK_Ordinary, SourceLocation(), false);
        IfStmt *S = duplicateIfStmt(ctxt, n, BO);
        RepairCandidate rc;
        rc.actions.clear();
        rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, S));
        if (!naive) {
            ExprListTy candidateVars = L->getCondCandidateVars(ori_cond->getLocEnd());
            rc.actions.push_back(RepairAction(newStatementLoc(loc, S), placeholder,
                    candidateVars));
        }
        // FIXME: priority!
        if (learning)
            rc.score = getLocScore(n);
        else
            rc.score = 4*PRIORITY_ALPHA;
        rc.kind = RepairCandidate::LoosenConditionKind;
        q.push_back(rc);

        if (naive) return;

        // FIXME: I think the best way is probably to decompose the condition,
        // but I am to lazy to do this.
        // This is to fix the case where they && to guard side-effect calls in
        // conditions.
        BinaryOperator *ori_BO = llvm::dyn_cast<BinaryOperator>(ori_cond);
        if (ori_BO)
            if (ori_BO->getOpcode() == BO_LAnd) {
                Expr* LHS = ori_BO->getLHS();
                Expr* RHS = ori_BO->getRHS();
                ParenExpr* ParenLHS = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), LHS);
                BinaryOperator *BO_LHS = new(*ctxt) BinaryOperator(ParenLHS,
                    placeholder, BO_LOr, ctxt->IntTy, VK_RValue,
                    OK_Ordinary, SourceLocation(), false);
                ParenExpr* ParenE = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), BO_LHS);
                BinaryOperator *BO = new(*ctxt) BinaryOperator(ParenE,
                    RHS, BO_LAnd, ctxt->IntTy, VK_RValue,
                    OK_Ordinary, SourceLocation(), false);
                IfStmt *S = duplicateIfStmt(ctxt, n, BO);
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, S));
                if (!naive) {
                    ExprListTy candidateVars = L->getCondCandidateVars(ori_cond->getLocEnd());
                    rc.actions.push_back(RepairAction(newStatementLoc(loc, S), placeholder,
                            candidateVars));
                }
                // FIXME: priority!
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = 4*PRIORITY_ALPHA;
                rc.kind = RepairCandidate::LoosenConditionKind;
                q.push_back(rc);
            }
    }

    void genAddMemset(Stmt* n, bool is_first) {
        if (in_yacc_func) return;
        if (naive) return;
        if (!hinfo.sys_memset) return;
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        ExprListTy exprs = L->getCandidatePointerForMemset(0);
        for (size_t i = 0; i < exprs.size(); i++) {
            // create sizeof() part
            ParenExpr *ParenE1 = new (*ctxt) ParenExpr(SourceLocation(),
                    SourceLocation(), exprs[i]);
            UnaryOperator *DerefUO = new(*ctxt)
                UnaryOperator(ParenE1, UO_Deref, exprs[i]->getType()->getPointeeType(),
                        VK_LValue, OK_Ordinary, SourceLocation());
            ParenExpr *ParenE2 = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), DerefUO);
            UnaryExprOrTypeTraitExpr *SizeofE = new (*ctxt) UnaryExprOrTypeTraitExpr(
                UETT_SizeOf, ParenE2, ctxt->UnsignedLongTy, SourceLocation(), SourceLocation());
            std::vector<Expr*> tmp_argv;
            tmp_argv.clear();
            tmp_argv.push_back(exprs[i]);
            tmp_argv.push_back(getNewIntegerLiteral(ctxt, 0));
            tmp_argv.push_back(SizeofE);
            CallExpr *CE = new(*ctxt) CallExpr(*ctxt, hinfo.sys_memset,
                    tmp_argv, ctxt->VoidPtrTy, VK_RValue, SourceLocation());
            if (L->isValidStmt(CE, NULL)) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::InsertMutationKind, CE));
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = getPriority(n) + PRIORITY_ALPHA;
                rc.kind = RepairCandidate::AddInitKind;
                rc.is_first = is_first;
                q.push_back(rc);
            }
        }
    }

    void genReplaceStmt(Stmt* n, bool is_first) {
        if (in_yacc_func) return;
        if (naive) return;
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        // OK, we limit replacement to expr only statement to avoid stupid redundent
        // changes to an compound statement/if statement
        if (llvm::isa<Expr>(n)) {
            AtomReplaceVisitor V(ctxt, L, n, ReplaceExt.getValue());
            V.TraverseStmt(n);
            std::set<Stmt*> res = V.getResult();
            for (std::set<Stmt*>::iterator it = res.begin(); it != res.end(); ++it) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, *it));
                // FIXME:
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = getPriority(n) + PRIORITY_ALPHA/2;
                rc.kind = RepairCandidate::ReplaceKind;
                rc.is_first = is_first;
                rc.oldRExpr = V.getOldRExpr(*it);
                rc.newRExpr = V.getNewRExpr(*it);
                q.push_back(rc);
            }
        }

        // We also attempt to replace string constant
        if (llvm::isa<Expr>(n)) {
            StringConstReplaceVisitor V(M, ctxt, n);
            V.TraverseStmt(n);
            std::set<std::pair<Stmt*, Expr*> > res = V.getResult();
            for (std::set<std::pair<Stmt*, Expr*> >::iterator it = res.begin(); it != res.end(); ++it) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, it->first));
                rc.actions.push_back(RepairAction(newStatementLoc(loc, it->first), it->second, std::vector<Expr*>()));
                rc.actions[rc.actions.size() - 1].tag = RepairAction::StringConstantTag;
                rc.is_first = is_first;
                rc.oldRExpr = V.getOldRExpr(it->first);
                rc.newRExpr = NULL;
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = getPriority(n) + PRIORITY_ALPHA + PRIORITY_ALPHA/2;
                rc.kind = RepairCandidate::ReplaceStringKind;
                q.push_back(rc);
            }
        }

        if (llvm::isa<Expr>(n)) {
            CallExprReplaceVisitor V2(ctxt, L, n);
            V2.TraverseStmt(n);
            std::vector<Stmt*> res2 = V2.getResult();
            for (std::vector<Stmt*>::iterator it = res2.begin();
                    it != res2.end(); ++ it) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, *it));
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = getPriority(n) + PRIORITY_ALPHA;
                rc.kind = RepairCandidate::ReplaceKind;
                rc.is_first = is_first;
                rc.oldRExpr = V2.getOldRExpr(*it);
                rc.newRExpr = V2.getNewRExpr(*it);
                q.push_back(rc);
            }
        }
    }

    void genAddStatement(Stmt* n, bool is_first, bool is_func_block) {
        if (in_yacc_func) return;
        if (naive) return;
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        std::set<Expr*> exprs = L->getGlobalCandidateExprs();
        std::map<std::string, RepairCandidate> tmp_map;
        tmp_map.clear();
        for (std::set<Expr*>::iterator it = exprs.begin(); it != exprs.end(); ++it) {
            AtomReplaceVisitor V(ctxt, L, *it, false);
            V.TraverseStmt(*it);
            std::set<Stmt*> stmts = V.getResult();
            Expr *subExpr = NULL;
            bool valid = L->isValidStmt(*it, &subExpr);
            // If it is not valid, and it contains more than
            // one invalid decl vars
            if (!valid && (subExpr == NULL))
                continue;

            for (std::set<Stmt*>::iterator it2 = stmts.begin(); it2 != stmts.end(); ++it2) {
                bool valid_after_replace = L->isValidStmt(*it2, NULL);
                if (!valid_after_replace) continue;
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc,
                            RepairAction::InsertMutationKind, *it2));
                if (learning) {
                    rc.score = getLocScore(n);
                }
                else {
                    rc.score = getPriority(n);
                    if (is_first) {
                        rc.score += PRIORITY_ALPHA;
                        if (is_func_block)
                            rc.score += PRIORITY_ALPHA/2;
                    }
                }
                rc.kind = RepairCandidate::AddAndReplaceKind;
                rc.is_first = is_first;
                tmp_map[stmtToString(*ctxt, *it2)] = rc;
            }
            if (valid) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc,
                            RepairAction::InsertMutationKind, *it));
                if (learning) {
                    rc.score = getLocScore(n);
                }
                else {
                    rc.score = getPriority(n);
                    if (is_first) {
                        rc.score += PRIORITY_ALPHA;
                        if (is_func_block)
                            rc.score += PRIORITY_ALPHA/2;
                    }
                }
                rc.kind = RepairCandidate::AddAndReplaceKind;
                rc.is_first = is_first;
                tmp_map[stmtToString(*ctxt, *it)] = rc;
            }
        }

#ifndef DISABLE_IFSTMT_INSERT
        // insert if_stmt without atom replace if possible
        std::set<Stmt*> stmts = L->getGlobalCandidateIfStmts();
        for (std::set<Stmt*>::iterator it = stmts.begin(); it != stmts.end(); ++it) {
            bool valid = L->isValidStmt(*it, NULL);
            if (valid) {
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc,
                            RepairAction::InsertMutationKind, *it));
                if (learning) {
                    rc.score = getLocScore(n);
                }
                else {
                    rc.score = getPriority(n);
                    if (is_first) {
                        rc.score += PRIORITY_ALPHA;
                        if (is_func_block)
                            rc.score += PRIORITY_ALPHA/2;
                    }
                }
                rc.kind = RepairCandidate::AddAndReplaceKind;
                rc.is_first = is_first;
                tmp_map[stmtToString(*ctxt, *it)] = rc;
            }
        }
#endif
        // This tmp_map is used to eliminate identical candidate generated
        for (std::map<std::string, RepairCandidate>::iterator it = tmp_map.begin();
                it != tmp_map.end(); ++it) {
            // see TraverseFuncDecl, some hacky way to fix loc score for is_first && is_func_block
            if (is_first && is_func_block)
                tmp_memo.push_back(q.size());
            q.push_back(it->second);
        }
    }

    void genAddIfGuard(Stmt* n, bool is_first) {
        if (in_yacc_func)
            return;
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        Expr* placeholder;
        if (naive)
            placeholder = getNewIntegerLiteral(ctxt, 1);
        else
            placeholder = M.getExprPlaceholder(ctxt, ctxt->IntTy);
        //clang::CallExpr *is_neg_call = L->getIsNegCall(hinfo.is_neg, getExpLineNumber(*ctxt, n));
        UnaryOperator *UO = new(*ctxt) UnaryOperator(placeholder,
                UO_LNot, ctxt->IntTy, VK_RValue, OK_Ordinary, SourceLocation());
        IfStmt *new_IF = new(*ctxt) IfStmt(*ctxt, SourceLocation(), NULL, UO, n);
        RepairCandidate rc;
        rc.actions.clear();
        rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, new_IF));
        if (!naive) {
            ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
            rc.actions.push_back(RepairAction(newStatementLoc(loc, new_IF), placeholder,
                    candidateVars));
        }
        // FIXME: priority!
        if (learning)
            rc.score = getLocScore(n);
        else
            rc.score = getPriority(n) + PRIORITY_ALPHA;
        rc.kind = RepairCandidate::GuardKind;
        rc.is_first = is_first;
        q.push_back(rc);
        if (naive) return;

        // for if statement, we also try guard the execution of the condition by adding
        // is_neg in before
        if (llvm::isa<IfStmt>(n))
            if (hasCallExpr(n)) {
                IfStmt* IfS = llvm::dyn_cast<IfStmt>(n);
                Expr *ori_cond = IfS->getCond();
                //assert(ori_cond->getType()->isIntegerType());
                UnaryOperator *UO = new(*ctxt) UnaryOperator(placeholder, UO_LNot,
                        ori_cond->getType(), VK_RValue, OK_Ordinary, SourceLocation());
                ParenExpr *ParenE = new(*ctxt) ParenExpr(SourceLocation(), SourceLocation(), ori_cond);
                BinaryOperator *BO = new(*ctxt) BinaryOperator(UO, ParenE, BO_LAnd, ctxt->IntTy,
                        VK_RValue, OK_Ordinary, SourceLocation(), false);
                IfStmt *new_IF = duplicateIfStmt(ctxt, IfS, BO);
                RepairCandidate rc;
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, new_IF));
                ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
                rc.actions.push_back(RepairAction(newStatementLoc(loc, new_IF), placeholder,
                            candidateVars));
                // FIXME: priority!
                if (learning)
                    rc.score = getLocScore(n);
                else
                    rc.score = getPriority(n) + PRIORITY_ALPHA;
                rc.kind = RepairCandidate::SpecialGuardKind;
                rc.is_first = is_first;
                q.push_back(rc);
            }
    }

    void genDeclStmtChange(DeclStmt *n) {
        if (naive) return;
        if (!n->isSingleDecl()) return;
        VarDecl *VD = llvm::dyn_cast<VarDecl>(n->getSingleDecl());
        if (!VD) return;
        QualType T = VD->getType();
        if (!T->isIntegerType()) return;
        VarDecl *newVD = VarDecl::Create(*ctxt, VD->getDeclContext(), SourceLocation(), SourceLocation(), VD->getIdentifier(), ctxt->DoubleTy, ctxt->getTrivialTypeSourceInfo(ctxt->DoubleTy),
                VD->getStorageClass());
        if (VD->getInit())
            newVD->setInit(VD->getInit());
        DeclStmt *newDS = new(*ctxt) DeclStmt(DeclGroupRef(newVD), SourceLocation(), SourceLocation());
        ASTLocTy loc = getNowLocation(n);
        RepairCandidate rc;
        rc.actions.clear();
        rc.actions.push_back(RepairAction(loc, RepairAction::ReplaceMutationKind, newDS));
        if (learning)
            rc.score = getLocScore(n);
        else
            rc.score = getPriority(n) + PRIORITY_ALPHA;
        rc.kind = RepairCandidate::ReplaceKind;
        rc.is_first = false;
        rc.oldRExpr = NULL;
        rc.newRExpr = NULL;
        q.push_back(rc);
    }

    void genAddIfExit(Stmt* n, bool is_first, bool is_func_block) {
        if (in_yacc_func)
            return;
        ASTLocTy loc = getNowLocation(n);
        LocalAnalyzer *L = M.getLocalAnalyzer(loc);
        Expr* placeholder;
        if (naive)
            placeholder = getNewIntegerLiteral(ctxt, 1);
        else
            placeholder = M.getExprPlaceholder(ctxt, ctxt->IntTy);
        //clang::CallExpr *is_neg_call = G->getIsNegCall(hinfo.is_neg, getExpLineNumber(*ctxt, n));
        //UnaryOperator *UO = new(*ctxt) UnaryOperator(hinfo.is_neg, UO_LNot, ctxt->IntTy, VK_RValue, OK_Ordinary, SourceLocation());
        FunctionDecl* curFD = L->getCurrentFunction();
        RepairCandidate rc;
        if (curFD->getCallResultType() == ctxt->VoidTy ) {
            ReturnStmt *RS = new(*ctxt) ReturnStmt(SourceLocation(), NULL, 0);
            IfStmt *IFS = new(*ctxt) IfStmt(*ctxt, SourceLocation(), 0, placeholder, RS);
            rc.actions.clear();
            rc.actions.push_back(RepairAction(loc, RepairAction::InsertMutationKind, IFS));
            if (!naive) {
                ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
                rc.actions.push_back(RepairAction(newStatementLoc(loc, IFS), placeholder,
                        candidateVars));
            }
            if (learning)
                rc.score = getLocScore(n);
            else {
                rc.score = getPriority(n) + PRIORITY_ALPHA;
                if (llvm::isa<LabelStmt>(n))
                    rc.score += PRIORITY_ALPHA/2;
               /* if (llvm::isa<IfStmt>(n))
                    rc.score -= PRIORITY_ALPHA/4;*/
                if (is_first) {
                    rc.score += PRIORITY_ALPHA;
                    if (is_func_block)
                        rc.score += PRIORITY_ALPHA/2;
                }
            }
            rc.kind = RepairCandidate::IfExitKind;
            rc.is_first = is_first;
            q.push_back(rc);
        }
        else {
            ExprListTy exprs = L->getCandidateReturnExpr();
            for (size_t i = 0; i < exprs.size(); i++) {
                Expr* placeholder2 = exprs[i];
                ReturnStmt *RS = new(*ctxt) ReturnStmt(SourceLocation(), placeholder2, 0);
                IfStmt *IFS = new(*ctxt) IfStmt(*ctxt, SourceLocation(), 0, placeholder, RS);
                rc.actions.clear();
                rc.actions.push_back(RepairAction(loc, RepairAction::InsertMutationKind, IFS));
                if (!naive) {
                    ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
                    rc.actions.push_back(RepairAction(newStatementLoc(loc, IFS), placeholder,
                            candidateVars));
                }
                //FIXME: candidate
                if (learning)
                    rc.score = getLocScore(n);
                else {
                    rc.score = getPriority(n) + PRIORITY_ALPHA;
                    if (llvm::isa<LabelStmt>(n))
                        rc.score += PRIORITY_ALPHA/2;
                    /*if (llvm::isa<IfStmt>(n))
                        rc.score -= PRIORITY_ALPHA/4;*/
                    if (is_first) {
                        rc.score += PRIORITY_ALPHA;
                        if (is_func_block)
                            rc.score += PRIORITY_ALPHA/2;
                    }
                }
                rc.kind = RepairCandidate::IfExitKind;
                rc.is_first = is_first;
                q.push_back(rc);
            }
        }
        if (naive) return;
        if (L->isInsideLoop()) {
            BreakStmt *BS = new(*ctxt) BreakStmt(SourceLocation());
            IfStmt *IFS = new(*ctxt) IfStmt(*ctxt, SourceLocation(), 0, placeholder, BS);
            rc.actions.clear();
            rc.actions.push_back(RepairAction(loc, RepairAction::InsertMutationKind, IFS));
            ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
            rc.actions.push_back(RepairAction(newStatementLoc(loc, IFS), placeholder,
                        candidateVars));
            //FIXME: score
            if (learning)
                rc.score = getLocScore(n);
            else {
                rc.score = getPriority(n) + PRIORITY_ALPHA;
                if (llvm::isa<LabelStmt>(n))
                    rc.score += PRIORITY_ALPHA/2;
                /*if (llvm::isa<IfStmt>(n))
                    rc.score -= PRIORITY_ALPHA/4;*/
                if (is_first)
                    rc.score += PRIORITY_ALPHA;
            }
            rc.kind = RepairCandidate::IfExitKind;
            rc.is_first = is_first;
            q.push_back(rc);
        }
        // insert if goto, this is beyond the reach of expr synthesizer,
        // so we need a loop
        std::vector<LabelDecl*> labels = L->getCandidateGotoLabels();
        for (size_t i = 0; i < labels.size(); i++) {
            // We are going to ignore yy generated labels, this is hacky
            std::string label_name = labels[i]->getName();
            if (label_name.substr(0,2) == "yy")
                continue;
            GotoStmt *GS = new(*ctxt) GotoStmt(labels[i], SourceLocation(), SourceLocation());
            IfStmt *IFS = new(*ctxt) IfStmt(*ctxt, SourceLocation(), 0, placeholder, GS);
            rc.actions.clear();
            rc.actions.push_back(RepairAction(loc, RepairAction::InsertMutationKind, IFS));
            ExprListTy candidateVars = L->getCondCandidateVars(n->getLocStart());
            rc.actions.push_back(RepairAction(newStatementLoc(loc, IFS), placeholder,
                        candidateVars));
            if (learning) {
                rc.score = getLocScore(n) + 1e-3;
            }
            else {
                rc.score = getPriority(n) + PRIORITY_ALPHA + 200;
                if (llvm::isa<LabelStmt>(n))
                    rc.score += PRIORITY_ALPHA/2;
                /*if (llvm::isa<IfStmt>(n))
                    rc.score -= PRIORITY_ALPHA/4;*/
                if (is_first)
                    rc.score += PRIORITY_ALPHA;
            }
            rc.kind = RepairCandidate::IfExitKind;
            rc.is_first = is_first;
            q.push_back(rc);
        }
    }

public:
    RepairCandidateGeneratorImpl(SourceContextManager &M, const std::string &file,
            const std::map<Stmt*, unsigned long> &locs,
            bool naive, bool learning):
        ctxt(M.getSourceContext(file)), M(M), file(file), loc_map(locs),
        hinfo(M.getInternalHandlerInfo(ctxt)), naive(naive), learning(learning) {
        compound_counter.clear();
        stmt_stack.clear();
        q.clear();
        in_yacc_func = false;
        GeoP = 0.01;
        loc_map1 = loc_map;
    }

    void setFlipP(double GeoP) {
        this->GeoP = GeoP;
    }
    bool TraverseStmt(Stmt *n) {
        stmt_stack.push_back(n);
        bool ret = RecursiveASTVisitor::TraverseStmt(n);
        stmt_stack.pop_back();
        return ret;
    }

    bool TraverseIfStmt(IfStmt *n) {
        bool ret = RecursiveASTVisitor::TraverseIfStmt(n);
        Stmt *ThenCS = n->getThen();
        Stmt *ElseCS = n->getElse();
        if (isTainted(n) || isTainted(ThenCS) || isTainted(ElseCS)) {
            if (loc_map1.count(n) == 0)
                loc_map1[n] = 10000000;
            if (loc_map1[n] > loc_map1[ThenCS])
                loc_map1[n] = loc_map1[ThenCS];
            if (loc_map1[n] > loc_map1[ElseCS])
                loc_map1[n] = loc_map1[ElseCS];
        }
        if (isTainted(n) || isTainted(ThenCS))
            genTightCondition(n);
        if (isTainted(n) || isTainted(ElseCS))
            genLooseCondition(n);
        return ret;
    }

    bool VisitStmt(Stmt *n) {
        if (llvm::isa<CompoundStmt>(n))
            return true;
        if (stmt_stack.size() > 1 && stmt_stack[stmt_stack.size() - 1] == n) {
            CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(stmt_stack[stmt_stack.size() - 2]);
            bool is_first = false;
            if (CS) {
                is_first = true;
                for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                    if (*it == n) break;
                    if (!llvm::isa<DeclStmt>(*it))
                        is_first = false;
                }
            }
            is_first = is_first && !llvm::isa<DeclStmt>(n);

            if (isTainted(n)) {
                if (llvm::isa<DeclStmt>(n) && in_float)
                    genDeclStmtChange(llvm::dyn_cast<DeclStmt>(n));
                // This is to compute whether Stmt n is the first
                // non-decl statement in a CompoundStmt
                genReplaceStmt(n, is_first);
                if (!llvm::isa<DeclStmt>(n) && !llvm::isa<LabelStmt>(n))
                    genAddIfGuard(n, is_first);
                genAddMemset(n, is_first);
                genAddStatement(n, is_first, stmt_stack.size() == 2);
                genAddIfExit(n, is_first, stmt_stack.size() == 2);
            }
            else if (llvm::isa<IfStmt>(n)) {
                IfStmt *IFS = llvm::dyn_cast<IfStmt>(n);
                Stmt* thenBlock = IFS->getThen();
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(thenBlock);
                Stmt* firstS = thenBlock;
                if (CS)
                    if (CS->body_begin() != CS->body_end())
                        firstS = *CS->body_begin();
                if (isTainted(thenBlock) || (firstS != NULL && isTainted(firstS))) {
                    if (isTainted(thenBlock))
                        loc_map1[n] = loc_map1[thenBlock];
                    else
                        loc_map1[n] = loc_map1[firstS];
                    genAddStatement(n, is_first, stmt_stack.size() == 2);
                }
            }
        }
        return true;
    }

    bool TraverseCompoundStmt(CompoundStmt *n) {
        bool ret = RecursiveASTVisitor::TraverseCompoundStmt(n);
        compound_counter[n] = 0;
        size_t best = 1000000;
        for (CompoundStmt::body_iterator it = n->body_begin(); it != n->body_end(); ++it) {
            if (isTainted(*it)) {
                compound_counter[n] ++;
                assert(loc_map1.count(*it) > 0);
                if (best > loc_map1[n])
                    best = loc_map1[n];
            }
        }
        loc_map1[n] = best;
        return ret;
    }

    class FloatChecker : public RecursiveASTVisitor<FloatChecker> {
        bool res;
    public:
        FloatChecker() { res = false; }

        bool VisitDeclRefExpr(DeclRefExpr *E) {
            if (E->getType()->isRealFloatingType())
                res = true;
            return true;
        }

        bool getResult() {
            return res;
        }
    };

    bool containsFloat(FunctionDecl *FD) {
        FloatChecker v;
        v.TraverseFunctionDecl(FD);
        return v.getResult();
    }

    bool TraverseFunctionDecl(FunctionDecl *FD) {
        in_yacc_func = isYaccFunc(FD);
        in_float = containsFloat(FD);
        // This is to fix the first statement in the function block,
        // a little bit hacky though, because we use a temporary memo<`2`> list
        tmp_memo.clear();
        bool ret = RecursiveASTVisitor::TraverseFunctionDecl(FD);
        for (size_t i = 0; i < tmp_memo.size(); i++) {
            RepairCandidate &rc = q[tmp_memo[i]];
            assert( rc.is_first );
            assert( rc.actions.size() > 0);
            unsigned long old_loc = loc_map1[rc.actions[0].loc.stmt];
            loc_map1[rc.actions[0].loc.stmt] = loc_map1[FD->getBody()];
            if (learning)
                rc.score = getLocScore(rc.actions[0].loc.stmt) + 0.2;
            else {
                rc.score += old_loc;
                rc.score -= loc_map1[rc.actions[0].loc.stmt];
            }
        }
        return ret;
    }

    std::vector<RepairCandidate> run() {
        TraverseDecl(ctxt->getTranslationUnitDecl());
        return q;
    }

};

std::string RepairCandidate::toString(SourceContextManager &M) const {
    std::ostringstream sout;
    sout << "Priority " << score << "\n";
    for (size_t i = 0; i < actions.size(); i++)
        if (!M.isNewStmt(actions[i].loc.stmt))
            sout << "At location " << actions[i].loc.toString(M) << "\n";
    CodeRewriter R(M, *this, NULL);
    std::map<std::string, std::vector<std::string> > patches = R.getPatches();
    for (std::map<std::string, std::vector<std::string> >::iterator it = patches.begin();
            it != patches.end(); ++it) {
        sout << "--Src File: " << it->first << "\n";
        for (size_t i = 0; i < it->second.size(); i++) {
            sout << "Fragment " << i << ":\n";
            sout << it->second[i] << "\n";
        }
    }
    return sout.str();
}

void RepairCandidate::dump() const {
    llvm::errs() << actions.size() << " actions\n";
    for (size_t i = 0; i < actions.size(); i++) {
        llvm::errs() << "loc stmt " << actions[i].loc.stmt << " kind "
            << actions[i].kind << " ast_node " << actions[i].ast_node << " ";
        if (actions[i].kind == RepairAction::ExprMutationKind) {
            llvm::errs() << "<";
            for (size_t j = 0; j < actions[i].candidate_atoms.size(); j++) {
                if (j != 0) llvm::errs() << ",";
                llvm::errs() << actions[i].candidate_atoms[j];
            }
            llvm::errs() << ">\n";
        }
        else
            llvm::errs() << "\n";
    }
}

RepairCandidateGenerator::RepairCandidateGenerator(SourceContextManager &M, const std::string &file,
        const std::map<clang::Stmt*, unsigned long> &locs, bool naive, bool learning) {
    impl = new RepairCandidateGeneratorImpl(M, file, locs, naive, learning);
}

RepairCandidateGenerator::~RepairCandidateGenerator() {
    delete impl;
}

std::vector<RepairCandidate> RepairCandidateGenerator::run() {
    return impl->run();
}

void RepairCandidateGenerator::setFlipP(double GeoP) {
    impl->setFlipP(GeoP);
}
