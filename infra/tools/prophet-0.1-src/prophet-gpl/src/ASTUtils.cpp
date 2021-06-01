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
#define ENABLE_DEBUG
#include "ASTUtils.h"
#include "BenchProgram.h"
#include "SourceContextManager.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/AST/Type.h>
#include <stdio.h>
#include <string>
#include <vector>

using namespace clang;

namespace {

std::string fix_indent(const std::string &res, size_t indent_cnt) {
    std::string ret="";
    for (size_t i = 0; i < res.size(); ++i) {
        ret.push_back(res[i]);
        if ((res[i] == '\n') && (i != res.size() - 1))
            ret += std::string(indent_cnt, ' ');
    }
   return ret;
}

class NaiveASTLocalizer : public RecursiveASTVisitor<NaiveASTLocalizer> {
    BenchProgram &P;
    ASTContext *ctxt;
    std::string filename;
    std::map<SourcePositionTy, Stmt*> res;
    const std::set<SourcePositionTy> &locs;

    void checkStmt(Stmt* n) {
        SourceLocation start = n->getLocStart();
        bool invalid = false;
        SourceLocation expand = ctxt->getSourceManager().getExpansionLoc(start);
        SourcePositionTy curLoc(P.normalizePath(ctxt->getSourceManager().getFilename(expand)),
          ctxt->getSourceManager().getExpansionLineNumber(start, &invalid));
        if (!invalid) {
            std::set<SourcePositionTy>::const_iterator it, start;
            start = locs.lower_bound(curLoc);
            for (it = start; it != locs.end(); it ++) {
                if ((it->expFilename == curLoc.expFilename) && (it->expLine == curLoc.expLine)) {
                    // We always settle with the first stmt we meet
                    if (res.count(*it) != 0)
                        continue;
                    res.insert(std::make_pair(*it, n));
                    break;
                }
                else
                    break;
            }
        }
    }

public:
    explicit NaiveASTLocalizer(BenchProgram &P, ASTContext *ctxt, const std::string &filename, const std::set<SourcePositionTy> &locs):
        P(P), ctxt(ctxt), filename(filename), locs(locs) {
        res.clear();
    }
    virtual ~NaiveASTLocalizer() { }

    virtual bool VisitIfStmt(IfStmt *IF) {
        if (IF == NULL) return true;
        Stmt* thenS = IF->getThen();
        Stmt* elseS = IF->getElse();
        if (thenS && !llvm::isa<CompoundStmt>(thenS))
            checkStmt(thenS);
        if (elseS && !llvm::isa<CompoundStmt>(elseS))
            checkStmt(elseS);
        return true;
    }

    virtual bool TraverseCompoundStmt(CompoundStmt *n) {
        // FIXME: We do not handle statement inside macro definition so far,
        // we just skip it!.
        SourceManager &M = ctxt->getSourceManager();
        SourceLocation start = n->getLocStart();
        SourceLocation end = n->getLocEnd();
        /*bool is_same_line = false;
        if (M.getFilename(M.getExpansionLoc(start)) == M.getFilename(M.getExpansionLoc(end)))
            if (M.getExpansionLineNumber(start) == M.getExpansionLineNumber(end))
                is_same_line = true;
        bool skip_inner = false;
        if (is_same_line) {
            if (M.getFilename(M.getExpansionLoc(start)) != M.getFilename(M.getSpellingLoc(start)))
                skip_inner = true;
            if (M.getExpansionLineNumber(start) != M.getSpellingLineNumber(start))
                skip_inner = true;
        }*/
        bool skip_inner = false;
        if (M.getExpansionLoc(start) == M.getExpansionLoc(end))
            skip_inner = true;
        if (skip_inner)
            return true;
        else {
            CompoundStmt *CS = n;
            for (CompoundStmt::body_iterator sit = CS->body_begin(); sit != CS->body_end(); ++sit) {
                Stmt *n = *sit;
                if (n == NULL) continue;
                if (llvm::isa<NullStmt>(n)) continue;
                checkStmt(n);
            }
            bool ret = RecursiveASTVisitor<NaiveASTLocalizer>::TraverseCompoundStmt(n);
            return ret;
        }
    }

    std::map<SourcePositionTy, Stmt*> getResult() {
        return res;
    }
};

}

std::map<SourcePositionTy, Stmt*> findCorrespondingStmt(BenchProgram &P, clang::ASTContext *ctxt,
        const std::string &filename, const std::set<SourcePositionTy> &locs) {
    ASTLocTy res;
    NaiveASTLocalizer Visitor(P, ctxt, filename, locs);
    Visitor.TraverseDecl(ctxt->getTranslationUnitDecl());
    return Visitor.getResult();
}

bool typeMatch(QualType Ta, QualType Tb) {
    if (Ta.isNull())
        return false;
    if (Ta->isReferenceType())
        return false;
    if (Tb.isNull())
        return true;
    if (!Ta.isAtLeastAsQualifiedAs(Tb))
        return false;
    return Ta.getCanonicalType().getTypePtr() == Tb.getCanonicalType().getTypePtr();
}

bool isZeroValue(Expr *E) {
    Expr *cur = E;
    while (llvm::isa<ImplicitCastExpr>(cur)) {
        ImplicitCastExpr *ICE = llvm::dyn_cast<ImplicitCastExpr>(cur);
        cur = ICE->getSubExpr();
    }
    IntegerLiteral *IL = llvm::dyn_cast<IntegerLiteral>(cur);
    if (IL) {
        return (IL->getValue() == 0);
    }
    return false;
}

size_t getExpLineNumber(ASTContext &C, clang::Stmt *S) {
    SourceManager &M = C.getSourceManager();
    SourceLocation SL = S->getLocStart();
    return M.getExpansionLineNumber(SL);
}

// We have this routine because the bug of pretty print when handling
// embedded asm statement
std::string fixASMInline(const std::string &str) {
    size_t cur_pos = 0;
    size_t idx;
    std::string ret = "";
    while ((idx = str.find("asm (", cur_pos)) != std::string::npos) {
        ret += str.substr(cur_pos, idx - cur_pos);
        // This is an asm statement
        ret += "__asm__(";
        int cnt = 0;
        size_t last_pos = idx + 4;
        for (size_t i = idx + 5; i < str.size(); i++) {
            if (str[i] == '(')
                cnt ++;
            if ((str[i] == ':' || str[i] == ')') && (cnt == 0)) {
                std::string para = stripLine(str.substr(last_pos + 1, i - last_pos - 1));
                last_pos = i;
                int j = para.size() - 1;
                while (j > 0) {
                    if (para[j] != '"')
                        j --;
                    else break;
                }
                if (para[j] != '"' || j == (int)(para.size() - 1))
                    ret += para + str[i];
                else {
                    ret += para.substr(0, j+1) + "(" + para.substr(j + 1) + ")" + str[i];
                }
                if (str[i] == ')') {
                    cur_pos = i + 1;
                    break;
                }
            }
            else if (str[i] == ')' && cnt > 0) {
                cnt --;
            }
        }
    }
    if (cur_pos < str.size())
        ret += str.substr(cur_pos);
    return ret;
}

std::string stmtToString(ASTContext &C, clang::Stmt* S) {
    if (S == NULL)
        return "NULL";
    std::string tmp;
    llvm::raw_string_ostream sout(tmp);
    S->printPretty(sout, 0, C.getPrintingPolicy());
    tmp = sout.str();
    return fixASMInline(tmp);
}

bool isSameStmt(ASTContext &C, Stmt* S1, Stmt* S2) {
    return stmtToString(C, S1) == stmtToString(C, S2);
}

namespace {

class EvalIntegerVisitor : public RecursiveASTVisitor<EvalIntegerVisitor> {
    Expr *E;
    long long &v;
    std::map<Expr*, long long> M;
public:
    EvalIntegerVisitor(Expr* E, long long &v): E(E), v(v), M() { }

    virtual bool TraverseStmt(Stmt *S) {
        return RecursiveASTVisitor::TraverseStmt(S);
    }

    virtual bool TraverseIntegerLiteral(IntegerLiteral *IL) {
        long long x = IL->getValue().getZExtValue();
        M[IL] = x;
        return RecursiveASTVisitor::TraverseIntegerLiteral(IL);
    }

    bool TraverseBinaryOperatorImpl(BinaryOperator *BO) {
        bool ret = RecursiveASTVisitor::TraverseBinaryOperator(BO);
        Expr *LHS = BO->getLHS();
        if (M.count(LHS) == 0) return ret;
        long long LHSv = M[LHS];
        Expr *RHS = BO->getRHS();
        if (M.count(RHS) == 0) return ret;
        long long RHSv = M[RHS];

        switch (BO->getOpcode()) {
            case BO_Mul:
                M[BO] = LHSv * RHSv;
                break;
            case BO_Div:
                // FIXME: something bad may happened,
                // but we just ignore
                if (RHSv == 0) return ret;
                M[BO] = LHSv / RHSv;
                break;
            case BO_Rem:
                if (RHSv == 0) return ret;
                M[BO] = LHSv % RHSv;
                break;
            case BO_Add:
                M[BO] = LHSv + RHSv;
                break;
            case BO_Sub:
                M[BO] = LHSv - RHSv;
                break;
            case BO_Shl:
                M[BO] = LHSv << RHSv;
                break;
            case BO_Shr:
                M[BO] = LHSv >> RHSv;
                break;
            case BO_And:
                M[BO] = LHSv & RHSv;
                break;
            case BO_Xor:
                M[BO] = LHSv ^ RHSv;
                break;
            case BO_Or:
                M[BO] = LHSv | RHSv;
                break;
            default:
                return ret;
        }
        return ret;
    }

#define OPERATOR(NAME) \
    virtual bool TraverseBin##NAME(BinaryOperator *BO) { \
        return TraverseBinaryOperatorImpl(BO); \
    }

    MY_BINOP_LIST()
#undef OPERATOR

    bool TraverseUnaryOperatorImpl(UnaryOperator *UO) {
        bool ret = RecursiveASTVisitor::TraverseUnaryOperator(UO);
        Expr *Sub = UO->getSubExpr();
        if (M.count(Sub) == 0) return ret;
        long long Subv = M[Sub];
        switch (UO->getOpcode()) {
            case UO_Plus:
                M[UO] = Subv;
                break;
            case UO_Minus:
                M[UO] = -Subv;
                break;
            case UO_Not:
                M[UO] = ~Subv;
                break;
            default:
                return ret;
        }
        return ret;
    }

#define OPERATOR(NAME) \
    virtual bool TraverseUnary##NAME(UnaryOperator *UO) { \
        return TraverseUnaryOperatorImpl(UO); \
    }

    MY_UNARYOP_LIST()
#undef OPERATOR

    bool TraverseParenExpr(ParenExpr *PE) {
        bool ret = RecursiveASTVisitor::TraverseParenExpr(PE);
        Expr *Sub = PE->getSubExpr();
        if (M.count(Sub) == 0) return ret;
        M[PE] = M[Sub];
        return ret;
    }

    virtual bool TraverseImplicitCastExpr(ImplicitCastExpr *ICE) {
        bool ret = RecursiveASTVisitor::TraverseImplicitCastExpr(ICE);
        if (M.count(ICE->getSubExpr()))
            M[ICE] = M[ICE->getSubExpr()];
        return ret;
    }

    bool setResult() {
        if (M.count(E) != 0) {
            v = M[E];
        }
        return M.count(E) != 0;
    }
};

}

bool evalIntegerConstant(Expr *E, long long &v) {
    EvalIntegerVisitor V(E, v);
    V.TraverseStmt(E);
    return V.setResult();
}

bool isIntegerConstant(Expr *E) {
    long long tmp;
    return evalIntegerConstant(E, tmp);
}

CompoundStmt* wrapStmtWithCompoundStmt(ASTContext &C, clang::Stmt *S) {
    std::vector<Stmt*> tmp_v;
    tmp_v.clear();
    tmp_v.push_back(S);
    CompoundStmt *new_CS = new (C) CompoundStmt(C, tmp_v, SourceLocation(), SourceLocation());
    return new_CS;
}

namespace {

class SimpleExprVisitor : public RecursiveASTVisitor<SimpleExprVisitor> {
    bool res;
public:
    SimpleExprVisitor() : res(true) { }

    virtual bool VisitBinAssign(BinaryOperator *) {
        res = false;
        return true;
    }

    virtual bool VisitCompoundAssignOperator(CompoundAssignOperator *) {
        res = false;
        return true;
    }

    virtual bool VisitCallExpr(CallExpr *) {
        res = false;
        return true;
    }

    bool isSimple() {
        return res;
    }
};

}

bool isSimpleExpr(Expr *E) {
    SimpleExprVisitor V;
    V.TraverseStmt(E);
    return V.isSimple();
}

std::string ASTLocTy::toString(SourceContextManager &M) const {
    SourceManager &SM = M.getSourceContext(filename)->getSourceManager();
    SourceLocation startLoc = stmt->getLocStart();
    SourceLocation expLoc = SM.getExpansionLoc(startLoc);
    std::ostringstream sout;
    sout << std::string(SM.getFilename(expLoc)) << ":" << SM.getExpansionLineNumber(startLoc);
    return sout.str();
}

class StmtReplacerImpl: public RecursiveASTVisitor<StmtReplacerImpl> {
    ASTContext *ctxt;
    Stmt *S;
    std::map<Stmt*, Stmt*> RM;
    bool force_rebuilt;
public:
    StmtReplacerImpl(ASTContext *ctxt, Stmt* S):
        ctxt(ctxt), S(S), RM(), force_rebuilt(false) { RM[0] = 0; }

    virtual ~StmtReplacerImpl() { }

    void addRule(Expr* a, Expr *b) {
        //llvm::errs() << "Adding rule: " << a << " " << b << "\n";
        //a->dump();
        //b->dump();
        RM.insert(std::make_pair(a,b));
    }

    virtual bool TraverseCaseStmt(CaseStmt *CS) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseCaseStmt(CS);
        Stmt *SubS = CS->getSubStmt();
        if ((RM[SubS] != SubS) || _force_rebuilt) {
            CaseStmt *newS = new (*ctxt) CaseStmt(CS->getLHS(), CS->getRHS(), SourceLocation(), SourceLocation(), SourceLocation());
            newS->setSubStmt(RM[SubS]);
            RM[CS] = newS;
        }
        else
            RM[CS] = CS;
        return ret;
    }

    virtual bool TraverseDefaultStmt(DefaultStmt *DS) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseDefaultStmt(DS);
        Stmt *SubS = DS->getSubStmt();
        if ((RM[SubS] != SubS) || _force_rebuilt) {
            DefaultStmt *newS = new (*ctxt) DefaultStmt(SourceLocation(), SourceLocation(), RM[SubS]);
            RM[DS] = newS;
        }
        else
            RM[DS] = DS;
        return ret;
    }

    virtual bool TraverseIfStmt(IfStmt *IFS) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        //IFS->dump();
        bool ret = RecursiveASTVisitor::TraverseIfStmt(IFS);
        Stmt* thenS = IFS->getThen();
        Stmt* elseS = IFS->getElse();
        Expr* condExpr = IFS->getCond();
        assert( RM.count(thenS) != 0);
        assert( RM[thenS] != 0);
        if ((RM[thenS] != thenS) || (RM[elseS] != elseS) || (RM[condExpr] != condExpr) || _force_rebuilt) {
            IfStmt *newS = new(*ctxt) IfStmt(*ctxt, SourceLocation(), IFS->getConditionVariable(),
                    llvm::dyn_cast<Expr>(RM[condExpr]), RM[thenS], SourceLocation(), RM[elseS]);
            RM[IFS] = newS;
        }
        else
            RM[IFS] = IFS;
        return ret;
    }

    virtual bool TraverseCompoundStmt(CompoundStmt *CS) {
        // NOTE: We are not going to go inside compound stmt
        RM[CS] = CS;
        return true;
    }

    virtual bool VisitExpr(Expr *E) {
        // By default, we just make E maps to E if not otherwise specified
        if (RM.count(E) == 0)
            RM[E] = E;
        return true;
    }

    virtual bool TraverseCallExpr(CallExpr *CE) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseCallExpr(CE);
        Expr *callee = CE->getCallee();
        bool same = (RM[callee] == callee);
        std::vector<Expr*> rebuilt_args;
        rebuilt_args.clear();
        for (CallExpr::arg_iterator it = CE->arg_begin(); it != CE->arg_end(); ++it) {
            if (RM[*it] != *it) {
                same = false;
            }
            rebuilt_args.push_back(llvm::dyn_cast<Expr>(RM[*it]));
        }
        if (!same || _force_rebuilt) {
            CallExpr *newE = new(*ctxt) CallExpr(*ctxt, llvm::dyn_cast<Expr>(RM[callee]),
                    llvm::ArrayRef<Expr*>(rebuilt_args), CE->getType(),
                    CE->getValueKind(), SourceLocation());
            RM[CE] = newE;
        }
        else
            RM[CE] = CE;
        return ret;
    }

    virtual bool TraverseBinaryOperatorImpl(BinaryOperator *BO) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseBinaryOperator(BO);
        Expr *LHS = BO->getLHS();
        Expr *RHS = BO->getRHS();
        if ((RM[LHS] != LHS) || (RM[RHS] != RHS) || _force_rebuilt) {
            Expr *newE = new(*ctxt) BinaryOperator(llvm::dyn_cast<Expr>(RM[LHS]), llvm::dyn_cast<Expr>(RM[RHS]), BO->getOpcode(),
                    BO->getType(), BO->getValueKind(), BO->getObjectKind(), SourceLocation(),
                    false);
            RM[BO] = newE;
        }
        else
            RM[BO] = BO;
        return ret;
    }

#define OPERATOR(NAME) \
    virtual bool TraverseBin##NAME(BinaryOperator *n) { \
        return TraverseBinaryOperatorImpl(n); \
    }
    MY_BINOP_LIST()
#undef OPERATOR

    virtual bool TraverseUnaryOperatorImpl(UnaryOperator *UO) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseUnaryOperator(UO);
        Expr *sub = UO->getSubExpr();
        if (RM[sub] != sub || _force_rebuilt) {
            Expr *newE = new(*ctxt) UnaryOperator(llvm::dyn_cast<Expr>(RM[sub]), UO->getOpcode(), UO->getType(),
                    UO->getValueKind(), UO->getObjectKind(), SourceLocation());
            RM[UO] = newE;
        }
        else
            RM[UO] = UO;
        return ret;
    }

#define OPERATOR(NAME) \
virtual bool TraverseUnary##NAME(UnaryOperator *UO) { \
    return TraverseUnaryOperatorImpl(UO); \
}
MY_UNARYOP_LIST()
#undef OPERATOR

    virtual bool TraverseCAOImpl(CompoundAssignOperator *CAO) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseCompoundAssignOperator(CAO);
        Expr *LHS = CAO->getLHS();
        Expr *RHS = CAO->getRHS();
        if (RM[LHS] != LHS || RM[RHS] != RHS || _force_rebuilt) {
            Expr *newE = new (*ctxt) CompoundAssignOperator(
                llvm::dyn_cast<Expr>(RM[LHS]), llvm::dyn_cast<Expr>(RM[RHS]), CAO->getOpcode(), CAO->getType(),
                CAO->getValueKind(), CAO->getObjectKind(), CAO->getComputationLHSType(),
                CAO->getComputationResultType(), SourceLocation(),
                false);
            RM[CAO] = newE;
        }
        else
            RM[CAO] = CAO;
        return ret;
    }

#define OPERATOR(NAME) \
    virtual bool TraverseBin##NAME##Assign(CompoundAssignOperator *CAO) { \
        return TraverseCAOImpl(CAO); \
    }

    MY_CAO_LIST()
#undef OPERATOR

    virtual bool TraverseReturnStmt(ReturnStmt *RS) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseReturnStmt(RS);
        Expr *V = RS->getRetValue();
        if (RM[V] != V || _force_rebuilt) {
            ReturnStmt *newS = new(*ctxt) ReturnStmt(SourceLocation(), llvm::dyn_cast<Expr>(RM[V]),
                    RS->getNRVOCandidate());
            RM[RS] = newS;
        }
        else
            RM[RS] = RS;
        return ret;
    }

    virtual bool TraverseParenExpr(ParenExpr *PE) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseParenExpr(PE);
        Expr *sub = PE->getSubExpr();
        if (RM[sub] != sub || _force_rebuilt) {
            ParenExpr *newE = new(*ctxt) ParenExpr(SourceLocation(), SourceLocation(), llvm::dyn_cast<Expr>(RM[sub]));
            RM[PE] = newE;
        }
        else
            RM[PE] = PE;
        return ret;
    }

    virtual bool TraverseImplicitCastExpr(ImplicitCastExpr *ICE) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseImplicitCastExpr(ICE);
        Expr *sub = ICE->getSubExpr();
        if (RM[sub] != sub || _force_rebuilt) {
            ImplicitCastExpr *newE = ImplicitCastExpr::Create(*ctxt, ICE->getType(),
                    ICE->getCastKind(), llvm::dyn_cast<Expr>(RM[sub]), 0, ICE->getValueKind());
            RM[ICE] = newE;
        }
        else
            RM[ICE] = ICE;
        return ret;
    }

    virtual bool TraverseMemberExpr(MemberExpr *ME) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseMemberExpr(ME);
        Expr *base = ME->getBase();
        if (RM[base] != base || _force_rebuilt) {
            MemberExpr *newE = new(*ctxt) MemberExpr(llvm::dyn_cast<Expr>(RM[base]), ME->isArrow(), ME->getMemberDecl(),
                    ME->getMemberNameInfo(), ME->getType(), ME->getValueKind(),
                    ME->getObjectKind());
            RM[ME] = newE;
        }
        else
            RM[ME] = ME;
        return ret;
    }

    virtual bool TraverseConditionalOperator(ConditionalOperator *CO) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseConditionalOperator(CO);
        Expr *Cond = CO->getCond();
        Expr *LHS = CO->getLHS();
        Expr *RHS = CO->getRHS();
        if ((RM[LHS] != LHS) || (RM[RHS] != RHS) || (RM[Cond] != Cond) ||
                (_force_rebuilt)) {
            ConditionalOperator *newCO = new(*ctxt) ConditionalOperator(
                    llvm::dyn_cast<Expr>(RM[Cond]), SourceLocation(),
                    llvm::dyn_cast<Expr>(RM[LHS]), SourceLocation(),
                    llvm::dyn_cast<Expr>(RM[RHS]), CO->getType(),
                    CO->getValueKind(), CO->getObjectKind());
            RM[CO] = newCO;
        }
        else
            RM[CO] = CO;
        return ret;
    }

    virtual bool TraverseArraySubscriptExpr(ArraySubscriptExpr *ASE) {
        bool _force_rebuilt = force_rebuilt;
        force_rebuilt = false;
        bool ret = RecursiveASTVisitor::TraverseArraySubscriptExpr(ASE);
        Expr *LHS = ASE->getLHS();
        Expr *RHS = ASE->getRHS();
        if ((RM[LHS] != LHS) || (RM[RHS] != RHS) || _force_rebuilt) {
            ArraySubscriptExpr *newE = new(*ctxt) ArraySubscriptExpr(llvm::dyn_cast<Expr>(RM[LHS]), llvm::dyn_cast<Expr>(RM[RHS]),
                    ASE->getType(), ASE->getValueKind(), ASE->getObjectKind(), SourceLocation());
            RM[ASE] = newE;
        }
        else
            RM[ASE] = ASE;
        return ret;
    }

    virtual bool TraverseStmt(Stmt* S) {
        if (RM.count(S) == 0) {
            RM[S] = S;
            return RecursiveASTVisitor::TraverseStmt(S);
        }
        else
            return true;
    }

    Stmt* getResult() {
        if (RM.count(S) == 0)
            TraverseStmt(S);
        return RM[S];
    }

    void setForceRebuilt() {
        force_rebuilt = true;
    }
};

StmtReplacer::StmtReplacer(ASTContext *ctxt, Stmt* S) {
    impl = new StmtReplacerImpl(ctxt, S);
}

StmtReplacer::~StmtReplacer() {
    delete impl;
}

void StmtReplacer::addRule(Expr *a, Expr *b) {
    impl->addRule(a, b);
}

Stmt* StmtReplacer::getResult() {
    return impl->getResult();
}

IntegerLiteral* getNewIntegerLiteral(ASTContext *ctxt, uint64_t v) {
    return IntegerLiteral::Create(*ctxt, llvm::APInt(32, v), ctxt->IntTy, clang::SourceLocation());
}

Stmt* duplicateStmt(ASTContext *ctxt, Stmt* S) {
    StmtReplacerImpl R(ctxt, S);
    R.setForceRebuilt();
    return R.getResult();
}

Expr* getParenExpr(ASTContext *ctxt, Expr* E) {
    if (llvm::isa<ParenExpr>(E))
        return E;
    else {
        ParenExpr *ParenE = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), E);
        return ParenE;
    }
}

Expr* stripParenAndCast(Expr* E) {
    if (!E) return E;
    Expr *ret = E;
    while (llvm::isa<ParenExpr>(ret) || llvm::isa<ImplicitCastExpr>(ret)) {
        ParenExpr *PE = llvm::dyn_cast<ParenExpr>(ret);
        if (PE)
            ret = PE->getSubExpr();
        else {
            ImplicitCastExpr *ICE = llvm::dyn_cast<ImplicitCastExpr>(ret);
            assert( ICE );
            ret = ICE->getSubExpr();
        }
        if (!ret) return NULL;
    }
    return ret;
}

class YaccFuncIdentifier : public RecursiveASTVisitor<YaccFuncIdentifier> {
    unsigned long yacc_cnt;
public:
    YaccFuncIdentifier() : RecursiveASTVisitor(), yacc_cnt(0) { }

    virtual bool VisitGotoStmt(GotoStmt *GS) {
        LabelStmt* LS = GS->getLabel()->getStmt();
        std::string labelName = LS->getName();
        if (labelName.substr(0, 2) == "yy")
            yacc_cnt ++;
        return !(yacc_cnt > 5);
    }

    virtual bool getResult() {
        return yacc_cnt > 5;
    }
};

bool isYaccFunc(FunctionDecl *FD) {
    YaccFuncIdentifier V;
    V.TraverseDecl(FD);
    return V.getResult();
}
