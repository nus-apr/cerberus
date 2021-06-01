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
#include "LocalAnalyzer.h"
#include "GlobalAnalyzer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "ASTUtils.h"
#include <map>

using namespace clang;

namespace {

typedef std::vector<Stmt*> StmtStackTy;

class StmtStackVisitor : public clang::RecursiveASTVisitor<StmtStackVisitor> {
    ASTLocTy loc;
    StmtStackTy curStmtStack, resStmtStack;
    FunctionDecl *curFunc, *resFunc;
public:
    StmtStackVisitor(ASTLocTy loc): loc(loc), curStmtStack(),
    resStmtStack(), curFunc(NULL), resFunc(NULL) { }
    ~StmtStackVisitor() {}
    virtual bool TraverseFunctionDecl(FunctionDecl *FD) {
        curFunc = FD;
        return RecursiveASTVisitor<StmtStackVisitor>::TraverseFunctionDecl(FD);
    }
    virtual bool TraverseStmt(Stmt *S) {
        curStmtStack.push_back(S);
        if (S == loc.stmt) {
            resStmtStack = curStmtStack;
            resFunc = curFunc;
            return false;
        }
        else {
            bool ret = RecursiveASTVisitor<StmtStackVisitor>::TraverseStmt(S);
            curStmtStack.pop_back();
            return ret;
        }
    }

    StmtStackTy getStmtStack() {
        return resStmtStack;
    }

    FunctionDecl *getEnclosingFunctionDecl() {
        return resFunc;
    }
};

class LocalActiveVarVisitor : public clang::RecursiveASTVisitor<LocalActiveVarVisitor> {
    std::set<Stmt*> StmtStackSet;
    FunctionDecl *curFD, *targetFD;
    Stmt* targetStmt;
    std::set<VarDecl*> invalidDeclSet;
    bool valid, pass;
public:
    LocalActiveVarVisitor(const StmtStackTy &stack, FunctionDecl *targetFD):
      StmtStackSet(stack.begin(), stack.end()), curFD(NULL),
      targetFD(targetFD), targetStmt(stack.back()), invalidDeclSet(), valid(true), pass(false) { }
    ~LocalActiveVarVisitor() { }

    virtual bool TraverseFunctionDecl(FunctionDecl *FD) {
        curFD = FD;
        return RecursiveASTVisitor<LocalActiveVarVisitor>::TraverseFunctionDecl(FD);
    }
    virtual bool TraverseStmt(Stmt *S) {
        if (S == NULL) return true;
        if (S == targetStmt)
            pass = true;
        if (valid)
            if (!llvm::isa<DeclStmt>(S) && (StmtStackSet.count(S) == 0)) {
                valid = false;
                bool ret = RecursiveASTVisitor<LocalActiveVarVisitor>::TraverseStmt(S);
                valid = true;
                return ret;
            }
        return RecursiveASTVisitor<LocalActiveVarVisitor>::TraverseStmt(S);
    }
    virtual bool VisitVarDecl(VarDecl *VD) {
        if ((!valid) || (curFD != targetFD) || pass) {
            invalidDeclSet.insert(VD);
        }
        return true;
    }

    std::set<VarDecl*> getValidLocalVarDeclSet() {
        std::set<VarDecl*> ret;
        ret.clear();
        for (DeclContext::decl_iterator it = targetFD->decls_begin(); it != targetFD->decls_end(); ++it) {
            VarDecl *VD = llvm::dyn_cast<VarDecl>(*it);
            if (VD)
                if (invalidDeclSet.count(VD) == 0)
                    ret.insert(VD);
        }
        return ret;
    }
};

class MemberExprStemVisitor : public RecursiveASTVisitor<MemberExprStemVisitor> {
    std::map<std::string, Expr*> res;
    ASTContext *ctxt;
public:
    MemberExprStemVisitor(ASTContext *ctxt): res(), ctxt(ctxt) {}
    ~MemberExprStemVisitor() {}
    virtual bool VisitMemberExpr(MemberExpr *ME) {
        // FIXME: This should maybe apply to all Expr, not just MemberExpr
        QualType QT = ME->getType();
        if (QT->isStructureType()) {
            // FIXME: a function for this!!
            std::string tmp = stripLine(stmtToString(*ctxt, ME));
            if ((tmp.size() < 2) || (tmp[0] != '-') || (tmp[1] != '-'))
                res[tmp] = ME;
        }
        Expr *base = ME->getBase();
        assert(base);
/*            const clang::RecordType *RecT = 0;
        if (!ME->isArrow())
            RecT = base->getType()->getAsStructureType();
        else {
            const PointerType *PT = llvm::dyn_cast<PointerType>(base->getType());
            RecT = llvm::dyn_cast<RecordType>(PT->getPointeeType().getTypePtr());
        }*/
        std::string tmp = stripLine(stmtToString(*ctxt, base));
        if ((tmp.size() < 2) || (tmp[0] != '-') || (tmp[1] != '-'))
            res[tmp] = base;
        return true;
    }

    virtual std::set<Expr*> getStemExprSet() {
        std::set<Expr*> ret;
        ret.clear();
        for (std::map<std::string, Expr*>::iterator it = res.begin(); it != res.end(); ++it)
            ret.insert(it->second);
        return ret;
    }
};

class ExprDisVisitor: public RecursiveASTVisitor<ExprDisVisitor> {
    ASTContext *ctxt;
    std::map<std::string, std::set<size_t> > &dis_map;
    SourceManager &M;
    std::string filename;
    //size_t expLine, expLine2;
public:
    ExprDisVisitor(ASTContext *ctxt, std::map<std::string, std::set<size_t> > &dis_map, ASTLocTy loc):
        ctxt(ctxt), dis_map(dis_map), M(ctxt->getSourceManager()) {
        SourceLocation SL = loc.stmt->getLocStart();
        SourceLocation expSL = M.getExpansionLoc(SL);
        filename = M.getFilename(expSL);
        /*expLine = M.getExpansionLineNumber(SL);
        SourceLocation SL_end = loc.stmt->getLocEnd();
        expLine2 = M.getExpansionLineNumber(SL_end);*/
    }

    virtual bool VisitExpr(Expr* E) {
        std::string tmp = stripLine(stmtToString(*ctxt, E));
        SourceLocation SL = E->getLocStart();
        SourceManager &M = ctxt->getSourceManager();
        SourceLocation expSL = M.getExpansionLoc(SL);
        if (M.getFilename(expSL) == filename) {
            /*size_t l = M.getExpansionLineNumber(SL);
            size_t dis = 0;
            if (l < expLine)
                dis = expLine - l;
            else if (l > expLine2)
                dis = l - expLine2;

            if (dis_map.count(tmp) == 0)
                dis_map[tmp] = dis;
            else if (dis_map[tmp] > dis)
                dis_map[tmp] = dis;*/
            dis_map[tmp].insert(M.getExpansionLineNumber(SL));
        }
        return true;
    }
};

class IntegerConstantVisitor: public RecursiveASTVisitor<IntegerConstantVisitor> {
    ASTContext *ctxt;
    std::set<long long> &s;
public:
    IntegerConstantVisitor(ASTContext *ctxt, std::set<long long> &s):
        ctxt(ctxt), s(s) { }

    virtual bool VisitExpr(Expr* E) {
        long long v = 0;
        if (evalIntegerConstant(E, v))
            s.insert(v);
        return true;
    }
};

class GotoLabelVisitor : public RecursiveASTVisitor<GotoLabelVisitor> {
    std::vector<clang::LabelDecl*> &labels;
public:
    GotoLabelVisitor(std::vector<clang::LabelDecl*> &l):
        labels(l) { }

    virtual bool VisitLabelStmt(LabelStmt *LS) {
        labels.push_back(LS->getDecl());
        return true;
    }
};

}

LocalAnalyzer::LocalAnalyzer(ASTContext *ctxt, GlobalAnalyzer *G, ASTLocTy loc, bool naive):
ctxt(ctxt), loc(loc), G(G), curFunc(NULL), LocalVarDecls(), MemberStems(), naive(naive) {
    StmtStackVisitor visitor1(loc);
    TranslationUnitDecl *TransUnit = ctxt->getTranslationUnitDecl();
    visitor1.TraverseDecl(TransUnit);
    curFunc = visitor1.getEnclosingFunctionDecl();

    StmtStackTy stmtStack = visitor1.getStmtStack();
    inside_loop = false;
    // Note that we exclude the last statement (itself)
    for (size_t i = 0; i < stmtStack.size() - 1; i++ ) {
        if (llvm::isa<ForStmt>(stmtStack[i]) || llvm::isa<WhileStmt>(stmtStack[i]) ||
            llvm::isa<DoStmt>(stmtStack[i])) {
            inside_loop = true;
            break;
        }
    }

    LocalActiveVarVisitor visitor2(stmtStack, curFunc);
    visitor2.TraverseDecl(TransUnit);
    LocalVarDecls = visitor2.getValidLocalVarDeclSet();
    /*for (std::set<VarDecl*>::iterator it = LocalVarDecls.begin(); it != LocalVarDecls.end(); ++it)
        (*it)->dump();*/

    MemberExprStemVisitor visitor3(ctxt);
    visitor3.TraverseFunctionDecl(curFunc);
    MemberStems = visitor3.getStemExprSet();

    ExprDis.clear();
    ExprDisVisitor visitor4(ctxt, ExprDis, loc);
    visitor4.TraverseFunctionDecl(curFunc);
    //for (std::set<Expr*>::iterator it = MemberStems.begin(); it != MemberStems.end(); ++it)
        //(*it)->dump();

    IntegerConstants.clear();
    // We start with 0 by default
    IntegerConstants.insert(0);
    IntegerConstantVisitor visitor5(ctxt, IntegerConstants);
    visitor5.TraverseFunctionDecl(curFunc);

    LocalLabels.clear();
    GotoLabelVisitor visitor6(LocalLabels);
    visitor6.TraverseFunctionDecl(curFunc);
}

LocalAnalyzer::ExprListTy LocalAnalyzer::genExprAtoms(QualType QT, bool allow_local, bool allow_glob, bool allow_field, bool allow_const, bool lvalue) {
    ExprListTy ret;
    ret.clear();
    const std::set<VarDecl*> &GlobalVarDecls = G->getGlobalVarDecls();
    const std::set<FunctionDecl*> &FuncDecls = G->getFuncDecls();
    // FIXME: This is some shit for C++
    //if (QT.isNull()) return ret;
    if (!QT.isNull() && QT->isReferenceType()) return ret;
    // Local direct variables
    if (allow_local) {
        for (std::set<VarDecl*>::iterator it = LocalVarDecls.begin(); it != LocalVarDecls.end(); ++it) {
            QualType localQT = (*it)->getType();
            if (typeMatch(localQT, QT)) {
                DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                        SourceLocation(), *it, false, SourceLocation(), localQT, VK_LValue);
                if (lvalue)
                    ret.push_back(DRE);
                else
                    ret.push_back(castToRValue(DRE));
            }
        }
    }
    // Global direct variables
    if (allow_glob) {
        for (std::set<VarDecl*>::const_iterator it = GlobalVarDecls.begin(); it != GlobalVarDecls.end(); ++it) {
            QualType globalQT = (*it)->getType();
            if (typeMatch(globalQT, QT)) {
                DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                        SourceLocation(), *it, false, SourceLocation(), globalQT, VK_LValue);
                if (lvalue)
                    ret.push_back(DRE);
                else
                    ret.push_back(castToRValue(DRE));
            }
        }
    }
    // Field reference
    if (allow_field) {
        // From existing stubs
        for (std::set<Expr*>::iterator it = MemberStems.begin(); it != MemberStems.end(); ++it) {
            Expr* E = *it;
            bool is_arrow = false;
            const Type *T = E->getType().getTypePtr();
            const RecordType *RT = NULL;
            if (T->isPointerType()) {
                RT = T->getPointeeType()->getAsStructureType();
                is_arrow = true;
            }
            else
                RT = T->getAsStructureType();
            if (RT) {
                RecordDecl* RD = RT->getDecl();
                if (RD) {
                    for (RecordDecl::decl_iterator dit = RD->decls_begin(); dit != RD->decls_end(); ++dit) {
                        FieldDecl *FD = llvm::dyn_cast<FieldDecl>(*dit);
                        if (FD) {
                            if (typeMatch(FD->getType(), QT)) {
                                MemberExpr *ME = new(*ctxt) MemberExpr(E, is_arrow, FD,
                                        DeclarationNameInfo(FD->getDeclName(), FD->getLocation()),
                                        FD->getType(), VK_LValue, OK_Ordinary);
                                if (lvalue)
                                    ret.push_back(ME);
                                else
                                    ret.push_back(castToRValue(ME));
                            }
                        }
                    }
                }
            }
        }
        // Form global variables
        for (std::set<VarDecl*>::iterator it = GlobalVarDecls.begin(); it != GlobalVarDecls.end(); ++it) {
            VarDecl *VD = *it;
            QualType T = VD->getType();
            bool is_arrow = false;
            const RecordType *RT = NULL;
            if (T->isPointerType()) {
                RT = T->getPointeeType()->getAsStructureType();
                is_arrow = true;
            }
            else
                RT = T->getAsStructureType();
            if (RT) {
                RecordDecl *RD = RT->getDecl();
                if (RD) {
                    for (RecordDecl::decl_iterator dit = RD->decls_begin(); dit != RD->decls_end(); ++dit) {
                        FieldDecl *FD = llvm::dyn_cast<FieldDecl>(*dit);
                        if (FD) {
                            if (typeMatch(FD->getType(), QT)) {
                                DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                                            SourceLocation(), VD, false, SourceLocation(), T, VK_LValue);
                                MemberExpr *ME = new(*ctxt) MemberExpr(DRE, is_arrow, FD,
                                        DeclarationNameInfo(FD->getDeclName(), FD->getLocation()),
                                        FD->getType(), VK_LValue, OK_Ordinary);
                                if (lvalue)
                                    ret.push_back(ME);
                                else
                                    ret.push_back(castToRValue(ME));
                            }
                        }
                    }
                }
            }
        }
    }
    // Constant reference
    // Now only consider 0
    if (allow_const && !lvalue && !QT.isNull()) {
        // FIXME: for now we don't handle boolean
        if (QT->isIntegerType() && !QT->isBooleanType()) {
            if (naive) {
                // We are going to try 0, -1
                IntegerLiteral *IL0 = getNewIntegerLiteral(ctxt, 0);
                ImplicitCastExpr *ICE = ImplicitCastExpr::Create(*ctxt, QT, CK_NullToPointer,
                        IL0, 0, VK_RValue);
                ret.push_back(ICE);
                IntegerLiteral *IL1 = getNewIntegerLiteral(ctxt, -1);
                ImplicitCastExpr *ICE1 = ImplicitCastExpr::Create(*ctxt, QT, CK_NullToPointer,
                        IL1, 0, VK_RValue);
                ret.push_back(ICE1);
            }
            else {
                for (std::set<long long>::iterator it = IntegerConstants.begin();
                        it != IntegerConstants.end(); ++it) {
                    IntegerLiteral *IL = getNewIntegerLiteral(ctxt, *it);
                    // FIXME: Add explicit cast if we want to handle boolean
                    ImplicitCastExpr *ICE = ImplicitCastExpr::Create(*ctxt, QT, CK_IntegralCast,
                            IL, 0, VK_RValue);
                    ret.push_back(ICE);
                }
            }
        }
        if (QT->isPointerType()) {
            IntegerLiteral *IL0 = getNewIntegerLiteral(ctxt, 0);
            ImplicitCastExpr *ICE = ImplicitCastExpr::Create(*ctxt, QT, CK_NullToPointer,
                    IL0, 0, VK_RValue);
            ret.push_back(ICE);
        }
        if (QT->isPointerType() || QT->isFunctionType()) {
            for (std::set<FunctionDecl*>::const_iterator it = FuncDecls.begin(); it != FuncDecls.end(); ++it) {
                QualType FT = (*it)->getType();
                if (typeMatch(FT, QT)) {
                    DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                        SourceLocation(), *it, false, SourceLocation(), FT, VK_RValue);
                    ret.push_back(DRE);
                }
                if (typeMatch(ctxt->getDecayedType(FT), QT)) {
                    DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                        SourceLocation(), *it, false, SourceLocation(), FT, VK_RValue);
                    ImplicitCastExpr *ICE = ImplicitCastExpr::Create(*ctxt, ctxt->getDecayedType(FT),
                            CK_FunctionToPointerDecay, DRE, 0, VK_RValue);
                    ret.push_back(ICE);
                }
            }
        }
    }
    return ret;
}

LocalAnalyzer::ExprListTy LocalAnalyzer::getCandidateCalleeFunction(CallExpr *CE, bool result_not_used) {
    ExprListTy ret;
    ret.clear();
    const std::set<FunctionDecl*> &FuncDecls = G->getFuncDecls();
    for (std::set<FunctionDecl*>::const_iterator it = FuncDecls.begin(); it != FuncDecls.end(); ++it) {
        FunctionDecl *FD = *it;
        if (CE->getCalleeDecl() == FD) continue;
        if (!FD->isVariadic()) {
            if (CE->getNumArgs() != FD->getNumParams())
                continue;
        }
        else {
            if (CE->getNumArgs() < FD->getNumParams())
                continue;
        }
        QualType FT = FD->getType();
        if (!FT->isFunctionProtoType())
            continue;
        //llvm::errs() << "checking name: " << FD->getName() << "\n";
        const FunctionProtoType *FPT = FT->getAs<FunctionProtoType>();
        if (!result_not_used)
            if (!typeMatch(CE->getType(), FPT->getCallResultType(*ctxt)))
                continue;
        //llvm::errs() << "Result match!" << "\n";
        size_t mismatch_cnt = 0;
        for (size_t i = 0; i < CE->getNumArgs(); i++) {
            if (i >= FD->getNumParams()) break;
            Expr *ArgE = CE->getArg(i);
            QualType argT = FPT->getParamType(i);
            if (isZeroValue(ArgE) && (argT->isPointerType() || argT->isIntegerType()))
                continue;
            if (!typeMatch(argT, ArgE->getType())) {
                mismatch_cnt ++;
                if (!argT->isPointerType() || !ArgE->getType()->isPointerType()) {
                    mismatch_cnt += 10;
                    break;
                }
                //llvm::errs() << "Arg " << i << " mismatch:\n";
                //ArgE->getType()->dump();
                //argT->dump();
            }
        }
        if (mismatch_cnt < 2 && mismatch_cnt < CE->getNumArgs()) {
            DeclRefExpr *DRE = DeclRefExpr::Create(*ctxt, NestedNameSpecifierLoc(),
                SourceLocation(), *it, false, SourceLocation(), FD->getType(), VK_RValue);
            ImplicitCastExpr *ICE = ImplicitCastExpr::Create(*ctxt, ctxt->getDecayedType(FD->getType()),
                    CK_FunctionToPointerDecay, DRE, 0, VK_RValue);
            ret.push_back(ICE);
        }
    }
    return ret;
}

LocalAnalyzer::ExprListTy LocalAnalyzer::getCandidatePointerForMemset(size_t max_dis) {
    ExprListTy ret;
    ret.clear();
    for (std::set<Expr*>::iterator it = MemberStems.begin(); it != MemberStems.end(); ++it) {
        Expr* E = *it;
        if (getExprDistance(E, loc.stmt) > max_dis) continue;
        QualType T = E->getType();
        if (T->isPointerType())
            ret.push_back(E);
        else {
            UnaryOperator *UO = new(*ctxt) UnaryOperator(E, UO_AddrOf,
                    ctxt->getPointerType(T), VK_RValue, OK_Ordinary, SourceLocation());
            ret.push_back(UO);
        }
    }
    return ret;
}

#define LARGE_DIS 1000000

size_t LocalAnalyzer::getExprDistance(Expr *E, size_t line_number) {
    std::string tmp = stripLine(stmtToString(*ctxt, E));
    if (ExprDis.count(tmp) == 0)
        return LARGE_DIS;
    else {
        std::set<size_t> &s = ExprDis[tmp];
        long long ret = LARGE_DIS;
        for (std::set<size_t>::iterator it = s.begin(); it != s.end(); it++) {
            //llvm::errs() << "Expr line: " << *it << "\n";
            //llvm::errs() << "Check line: " << line_number << "\n";
            if (abs((long long)line_number - *it) < ret)
                ret = abs((long long)line_number - *it);
        }
        return (size_t)ret;
    }
}

size_t LocalAnalyzer::getExprDistance(Expr *E, Stmt* S) {
    std::string tmp = stripLine(stmtToString(*ctxt, E));
    if (ExprDis.count(tmp) == 0)
        return LARGE_DIS;
    else {
        SourceLocation SL = loc.stmt->getLocStart();
        SourceManager &M = ctxt->getSourceManager();
        size_t expLine = M.getExpansionLineNumber(SL);
        SourceLocation SL_end = loc.stmt->getLocEnd();
        size_t expLine2 = M.getExpansionLineNumber(SL_end);

        std::set<size_t> &s = ExprDis[tmp];
        size_t ret = LARGE_DIS;
        for (std::set<size_t>::iterator it = s.begin(); it != s.end(); it++) {
            size_t l = *it;
            size_t dis = 0;
            if (l < expLine)
                dis = expLine - l;
            else if (l > expLine2)
                dis = l - expLine2;

            if (ret > dis)
                ret = dis;
        }
        return ret;
    }
}

namespace {

class StmtChecker : public RecursiveASTVisitor<StmtChecker> {
    LocalAnalyzer *L;
    GlobalAnalyzer *G;
    std::set<VarDecl*> inside;
    std::set<Expr*> invalidExprs;
public:
    StmtChecker(LocalAnalyzer *L, GlobalAnalyzer *G): L(L), G(G) {
        inside.clear();
        invalidExprs.clear();
    }

    virtual bool VisitVarDecl(VarDecl *VD) {
        inside.insert(VD);
        return true;
    }

    virtual bool VisitDeclRefExpr(DeclRefExpr *DRE) {
        ValueDecl *VD = DRE->getDecl();
        if (llvm::isa<FieldDecl>(VD)) return true;
        if (llvm::isa<EnumConstantDecl>(VD)) return true;

        bool found = false;
        VarDecl *VarD = llvm::dyn_cast<VarDecl>(VD);
        if (VarD) {
            if (L->getLocalVarDecls().count(VarD) != 0)
                found = true;
            if (G->getGlobalVarDecls().count(VarD) != 0)
                found = true;
            if (inside.count(VarD) != 0)
                found = true;
        }
        FunctionDecl *FuncD = llvm::dyn_cast<FunctionDecl>(VD);
        if (FuncD) {
            if (G->getFuncDecls().count(FuncD) != 0)
                found = true;
        }

        if (!found) {
            invalidExprs.insert(DRE);
            //llvm::errs() << "Not found:";
            //DRE->dump();
            //llvm::errs() << "\n";
        }
        return true;
    }

    std::set<Expr*> getResult() {
        return invalidExprs;
    }
};

}

bool LocalAnalyzer::isValidStmt(Stmt* S, Expr** invalidE) {
    BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(S);
    std::set<Expr*> res;
    // If this is binary operator, we must assume LHS is fine
    if (BO && (BO->getOpcode() == BO_Assign)) {
        StmtChecker V(this, G);
        V.TraverseStmt(BO->getLHS());
        res = V.getResult();
        if (res.size() != 0) {
            if (invalidE != NULL)
                *invalidE = NULL;
            return false;
        }
    }

    StmtChecker V(this, G);
    V.TraverseStmt(S);
    res = V.getResult();
    if (invalidE == NULL)
        return res.size() == 0;
    else {
        if (BO && (BO->getOpcode() == BO_Assign)) {
            if (res.size() > 2) {
                *invalidE = BO->getRHS();
                return false;
            }
            else if (res.size() == 1) {
                *invalidE = *res.begin();
                return false;
            }
            else {
                *invalidE = NULL;
                return true;
            }
        }
        if (res.size() == 1)
            *invalidE = *res.begin();
        else
            *invalidE = NULL;
        return res.size() == 0;
    }
}

std::set<Expr*> LocalAnalyzer::getCandidateInsertExprs() {
    std::set<Expr*> ret;
    const std::set<Expr*> &exprs = G->getCandidateExprs();
    for (std::set<Expr*>::const_iterator it = exprs.begin(); it != exprs.end(); ++it) {
        if (isValidStmt(*it, NULL))
            ret.insert(*it);
    }
    return ret;
}

std::set<Stmt*> LocalAnalyzer::getCandidateMacroExps() {
    std::set<Stmt*> ret;
    const std::set<Stmt*> &stmts = G->getCandidateMacroExps();
    for (std::set<Stmt*>::const_iterator it = stmts.begin(); it != stmts.end(); ++it) {
        if (isValidStmt(*it, NULL))
            ret.insert(*it);
    }
    return ret;
}

std::set<Expr*> LocalAnalyzer::getGlobalCandidateExprs() {
    std::set<Expr*> exprs = G->getCandidateExprs();
    std::set<Expr*> res;
    res.clear();
    for (std::set<Expr*>::iterator it = exprs.begin(); it != exprs.end(); ++it)
        res.insert(llvm::dyn_cast<Expr>(duplicateStmt(ctxt, *it)));
    return res;
}

std::set<Stmt*> LocalAnalyzer::getGlobalCandidateIfStmts() {
    std::set<Stmt*> stmts = G->getCandidateIfStmts();
    std::set<Stmt*> res;
    res.clear();
    for (std::set<Stmt*>::iterator it = stmts.begin(); it != stmts.end(); ++it)
        res.insert(duplicateStmt(ctxt, *it));
    return res;
}

LocalAnalyzer::ExprListTy LocalAnalyzer::getCandidateEnumConstant(EnumConstantDecl *ECD) {
    return G->getCandidateEnumConstant(ECD);
}

LocalAnalyzer::ExprListTy LocalAnalyzer::getCondCandidateVars(SourceLocation SL) {
    SourceManager &SM = ctxt->getSourceManager();
    bool invalid = false;
    size_t line_number = SM.getExpansionLineNumber(SL, &invalid);
    assert( !invalid);
    ExprListTy exprs = genExprAtoms(QualType(), true, true, true, false, true);
    ExprListTy ret;
    ret.clear();
    std::vector< std::pair<size_t, Expr*> > tmp_v;
    tmp_v.clear();
    for (size_t i = 0; i < exprs.size(); i++) {
        //exprs[i]->dump();
        QualType QT = exprs[i]->getType();
        if (!QT->isIntegerType() && !QT->isPointerType()) continue;
        //llvm::errs() << "Type correct!\n";
        MemberExpr *ME = llvm::dyn_cast<MemberExpr>(exprs[i]);
        if (ME) {
            size_t dis1 = getExprDistance(ME->getBase(), line_number);
            //llvm::errs() << "Dis1: " << dis1 << "\n";
            if (dis1 > 1)
                continue;
        }
        //llvm::errs() << "Member expr checking correct!\n";
        DeclRefExpr *DRE = llvm::dyn_cast<DeclRefExpr>(exprs[i]);
        if (DRE) {
            if (DRE->getDecl()->getName() != "argc")
                if (getExprDistance(DRE, loc.stmt) > 1000) continue;
        }
        //llvm::errs() << "Distance checking correct\n";
        if (isValidStmt(exprs[i], NULL)) {
            //llvm::errs() << "Valid, passed!\n";
            tmp_v.push_back(std::make_pair(getExprDistance(exprs[i], line_number), exprs[i]));
        }
    }
    sort(tmp_v.begin(), tmp_v.end());
    for (size_t i = 0; i < tmp_v.size(); i++)
        ret.push_back(tmp_v[i].second);
    return ret;
}

/*CallExpr* LocalAnalyzer::getIsNegCall(clang::Expr* is_neg_fn, size_t line_number) {
    std::vector<Expr*> tmp_argv;
    ExprListTy exprs = getIsNegVarList(line_number);
    tmp_argv.clear();
    tmp_argv.push_back(getNewIntegerLiteral(exprs.size()));
    for (size_t i = 0; i < exprs.size(); ++i) {
        ParenExpr *ParenE1 = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), exprs[i]);
        UnaryOperator *AddrsOf = new (*ctxt)
            UnaryOperator(ParenE1, UO_AddrOf, ctxt->getPointerType(exprs[i]->getType()),
                    VK_RValue, OK_Ordinary, SourceLocation());
        tmp_argv.push_back(AddrsOf);
        ParenExpr *ParenE2 = new (*ctxt) ParenExpr(SourceLocation(), SourceLocation(), exprs[i]);
        UnaryExprOrTypeTraitExpr *SizeofE = new (*ctxt) UnaryExprOrTypeTraitExpr(
            UETT_SizeOf, ParenE2, ctxt->UnsignedLongTy, SourceLocation(), SourceLocation());
        tmp_argv.push_back(SizeofE);
    }
    CallExpr *CE = new(*ctxt) CallExpr(*ctxt, is_neg_fn, tmp_argv,
            ctxt->IntTy, VK_RValue, SourceLocation());
    return CE;
}*/

/*#define MAGIC_NUMBER -123456789

bool checkV(const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
    const std::set<unsigned long> &negative_cases, const std::set<unsigned long> &positive_cases,
    const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
    size_t idx, long long v, int flag) {

    for (std::set<unsigned long>::iterator it = positive_cases.begin();
            it != positive_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator cit;
        cit = caseVMap.find(*it);
        assert( cit != caseVMap.end());
        for (size_t i = 0; i < cit->second.size(); i++) {
            if (cit->second[i][idx] == MAGIC_NUMBER)
                return false;
            if (((flag == 0) && (cit->second[i][idx] != v)) ||
                ((flag == 1) && (cit->second[i][idx] == v)))
                return false;
        }
    }

    for (std::set<unsigned long>::iterator it = negative_cases.begin();
            it != negative_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator cit;
        cit = caseVMap.find(*it);
        assert( cit != caseVMap.end());
        std::map<unsigned long, std::vector<unsigned long> >::const_iterator nit;
        nit = negative_records.find(*it);
        if (cit->second.size() != nit->second.size()) {
            outlog_printf(1, "Seems some non-determinism! %lu v.s. %lu Length mismatch!\n",
                    (unsigned long)cit->second.size(), (unsigned long)nit->second.size());
            return false;
        }
        for (size_t i = 0; i < cit->second.size(); i++) {
            if (cit->second[i][idx] == MAGIC_NUMBER)
                return false;
            bool cond = ((flag == 0) && (cit->second[i][idx] != v)) ||
                    ((flag == 1) && (cit->second[i][idx] == v));
            if ((nit->second[i] == 0) && (cond))
                return false;
            if ((nit->second[i] == 1) && (!cond))
                return false;
        }
    }
    return true;
}*/

/*
Expr* LocalAnalyzer::synthesizeResult(ExprListTy exprs,
        const std::map<unsigned long, std::vector<unsigned long> > &negative_records,
        const std::map<unsigned long, std::vector< std::vector< long long> > > &caseVMap,
        const std::set<unsigned long> &negative_cases,
        const std::set<unsigned long> &positive_cases) {
    // If just remove work, then we remove it
    bool got0 = false, got1 = false;
    size_t id0 = 0;
    size_t case_id0 = 0;
    size_t id1 = 0;
    size_t case_id1 = 0;
    for (std::set<unsigned long>::const_iterator it = positive_cases.begin();
            it != positive_cases.end(); ++it) {
        std::map<unsigned long, std::vector< std::vector< long long> > >::const_iterator find_it;
        find_it = caseVMap.find(*it);
        assert( find_it != caseVMap.end());
        if (find_it->second.size() != 0) {
            got0 = true;
            id0 = *it;
            case_id0 = 0;
            break;
        }
    }

    for (std::set<unsigned long>::const_iterator it = negative_cases.begin();
            it != negative_cases.end(); ++it) {
        std::map<unsigned long, std::vector<std::vector< long long> > >::const_iterator find_it;
        find_it = caseVMap.find(*it);
        assert( find_it != caseVMap.end());

        std::map<unsigned long, std::vector<unsigned long> >::const_iterator rit =
            negative_records.find(*it);
        assert( rit != negative_records.end());
        const std::vector<unsigned long> &tmpv = rit->second;
        for (size_t j = 0; j < tmpv.size(); j++) {
            if ((tmpv[j] == 0) && (!got0)) {
                got0 = true;
                id0 = *it;
                case_id0 = j;
            }
            if ((tmpv[j] == 1) && (!got1)) {
                got1 = true;
                id1 = *it;
                case_id1 = j;
            }
        }
    }

    assert( got1);
    if (!got0 && disabled_res.count(SynResTy(0, 1, 2)) == 0) {
        last_res = SynResTy(0, 1, 2);
        return getNewIntegerLiteral(ctxt, 1);
    }

    //const std::set<VarDecl*> &GlobalVarDecls = G->getGlobalVarDecls();

    bool found = false;
    long long resv = 0;
    size_t resi = 0;
    int res_flag = 0;

    for (size_t i = 0; i < exprs.size(); i++) {
        std::map<unsigned long, std::vector< std::vector<long long > > >::const_iterator
            find_it = caseVMap.find(id0);
	    long long v = 0;
        if (find_it != caseVMap.end()) {
		const std::vector< std::vector< long long> > &M = find_it->second;
		assert(M.size() > 0);
		v = M[case_id0][i];

		if (abs(v) < 1000)
		    if (disabled_res.count(SynResTy(i, v, 0)) == 0)
			if (checkV(caseVMap, negative_cases, positive_cases, negative_records, i, v, 0))
			    if (!found || ((v == 0) && (resv != 0))) {
				resv = v;
				resi = i;
				res_flag = 0;
				found = true;
			    }
	}

        find_it = caseVMap.find(id1);
        assert( find_it != caseVMap.end());
        if (find_it != caseVMap.end()) {
            v = find_it->second[case_id1][i];
            if (abs(v) < 1000)
                if (disabled_res.count(SynResTy(i, v, 1)) == 0)
                    if (checkV(caseVMap, negative_cases, positive_cases, negative_records, i, v, 1))
                        if (!found || ((v == 0) && (resv != 0))) {
                            resv = v;
                            resi = i;
                            res_flag = 1;
                            found = true;
                        }
        }
    }

    last_res = SynResTy(resi, resv, res_flag);

    if (found) {
        BinaryOperator *BO;
        if (res_flag == 1)
            BO = new(*ctxt) BinaryOperator(
                exprs[resi], getNewIntegerLiteral(ctxt, resv), BO_EQ, ctxt->IntTy, VK_RValue,
                OK_Ordinary, SourceLocation(), false);
        else {
            BO = new(*ctxt) BinaryOperator(
                exprs[resi], getNewIntegerLiteral(ctxt, resv), BO_NE, ctxt->IntTy, VK_RValue,
                OK_Ordinary, SourceLocation(), false);
        }
        return BO;
    }

    return NULL;
}

void LocalAnalyzer::lastSynthesizeFailed() {
    //llvm::errs() << "Adding: " << last_res.idx << " " <<
    //    last_res.v << " " << last_res.flag << "\n";
    disabled_res.insert(last_res);
}*/
