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
#include "FeatureVector.h"
#include "FeatureParameter.h"
#include "RepairCandidateGenerator.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "ASTUtils.h"
#include "LocalAnalyzer.h"
#include "llvm/Support/CommandLine.h"
#include <string>

llvm::cl::opt<bool> DisableModificationFeatures("disable-mod", llvm::cl::init(false),
    llvm::cl::desc("Disable Modification Features."));
llvm::cl::opt<bool> DisableSemanticCrossFeatures("disable-sema-cross", llvm::cl::init(false),
    llvm::cl::desc("Diable Semantic Features, setting them all zero!"));
llvm::cl::opt<bool> DisableSemanticValueFeatures("disable-sema-value", llvm::cl::init(false),
    llvm::cl::desc("Disable Semantic-Value Features, setting them all zero!"));

using namespace clang;

namespace {

enum RepairFeatureKind {
    CondRepair = 0,
    GuardRepair,
    AddControlRepair,
    AddStmtRepair,
    ReplaceStmtRepair,
    RepairFeatureEnd
};

const size_t MAX_REPAIR_FEATURE_KIND = RepairFeatureEnd;

std::string repairFidToString(unsigned int fid) {
    switch (fid) {
        case CondRepair:
            return "CondRepair";
        case GuardRepair:
            return "GuardRepair";
        case AddControlRepair:
            return "AddControlRepair";
        case AddStmtRepair:
            return "AddStmtRepair";
        case ReplaceStmtRepair:
            return "ReplaceStmtRepair";
        default:
            assert(0);
    }
    return "";
}

enum AtomFeatureKind {
    AddOpAF = 0,
    SubOpAF,
    MulOpAF,
    DivOpAF,
    LessOpAF,
    GreaterOpAF,
    EqOpAF,
    IncUOpAF,
    DecUOpAF,
    AddrOfAF,
    DerefAF,
    MemberAccessAF,
    IndexAF,
    ChangedAF,
    AssignLHSAF,
    AssignConstantAF,
    AssignZeroAF,
    CalleeAF,
    CallArgumentAF,
    AbstVAF,
    StmtIfAF,
    StmtAssignAF,
    StmtCallAF,
    StmtLoopAF,
    StmtControlAF,
    StmtLabelAF,
    RStmtCondAF,
    RStmtAssignAF,
    RStmtCallAF,
    RStmtControlAF,
    AtomFeatureEnd
};

const size_t MAX_ATOM_FEATURE_KIND = AtomFeatureEnd;

std::string atomFidToString(unsigned int fid) {
    switch (fid) {
        case AddOpAF:
            return "AddOpAF";
        case SubOpAF:
            return "SubOpAF";
        case MulOpAF:
            return "MulOpAF";
        case DivOpAF:
            return "DivOpAF";
        case LessOpAF:
            return "LessOpAF";
        case GreaterOpAF:
            return "GreaterOpAF";
        case EqOpAF:
            return "EqOpAF";
        case IncUOpAF:
            return "IncUOpAF";
        case DecUOpAF:
            return "DecUOpAF";
        case AddrOfAF:
            return "AddrOfAF";
        case DerefAF:
            return "DerefAF";
        case MemberAccessAF:
            return "MemberAccessAF";
        case IndexAF:
            return "IndexAF";
        case ChangedAF:
            return "ChangedAF";
        case AssignLHSAF:
            return "AssignLHSAF";
        case AssignConstantAF:
            return "AssignConstantAF";
        case AssignZeroAF:
            return "AssignZeroAF";
        case CalleeAF:
            return "CalleeAF";
        case CallArgumentAF:
            return "CallArgumentAF";
        case AbstVAF:
            return "AbstVAF";
        case StmtIfAF:
            return "StmtIfAF";
        case StmtAssignAF:
            return "StmtAssignAF";
        case StmtCallAF:
            return "StmtCallAF";
        case StmtLoopAF:
            return "StmtLoopAF";
        case StmtControlAF:
            return "StmtControlAF";
        case StmtLabelAF:
            return "StmtLabelAF";
        case RStmtCondAF:
            return "RStmtCondAF";
        case RStmtAssignAF:
            return "RStmtAssignAF";
        case RStmtCallAF:
            return "RStmtCallAF";
        case RStmtControlAF:
            return "RStmtControlAF";
        default:
            llvm::errs() << "Unknown atom feature id: " << fid << "\n";
            assert(0);
    }
    return "";
}

enum ValueFeatureKind {
    ModifiedVF = 0,
    ModifiedSimilarVF,
    FuncArgumentVF,
    LocalVarVF,
    GlobalVarVF,
    MemberVF,
    LenLiteralVF,
    PointerVF,
    StructPointerVF,
    ZeroConstVF,
    NonZeroConstVF,
    StringLiteralVF,
    ValueFeatureEnd
};

const size_t MAX_VALUE_FEATURE_KIND = ValueFeatureEnd;

std::string valueFidToString(unsigned int fid) {
    switch (fid) {
        case ModifiedVF:
            return "ModifiedVF";
        case ModifiedSimilarVF:
            return "ModifiedSimilarVF";
        case FuncArgumentVF:
            return "FuncArgumentVF";
        case LocalVarVF:
            return "LocalVarVF";
        case GlobalVarVF:
            return "GlobalVarVF";
        case MemberVF:
            return "MemberVF";
        case LenLiteralVF:
            return "LenLiteralVF";
        case PointerVF:
            return "PointerVF";
        case StructPointerVF:
            return "StructPointerVF";
        case ZeroConstVF:
            return "ZeroConstVF";
        case NonZeroConstVF:
            return "NonZeroConstVF";
        case StringLiteralVF:
            return "StringLiteralVF";
        default:
            assert(0);
    }
    return "";
}

bool isAbstractStub(Expr *E) {
    CallExpr *CE = llvm::dyn_cast<CallExpr>(stripParenAndCast(E));
    if (!CE) return false;
    FunctionDecl *FD = CE->getDirectCallee();
    if (FD) {
        return FD->getDeclName().isIdentifier() && ((FD->getName() == IS_NEG_HANDLER) || (FD->getName() == UNKNOWN_HOOK));
    }
    else
        return false;
}

class FeatureExtractVisitor : public RecursiveASTVisitor<FeatureExtractVisitor> {
    typedef std::multimap<unsigned int, unsigned int> HelperMapTy;
    const static HelperMapTy binOpHelper, uOpHelper, caOpHelper;
    ASTContext *ast;
    ValueToFeatureMapTy res;
    std::vector<Stmt*> stmtStack;
    bool isReplace;
    Expr* abst_v;
    bool is_replace_strconst;
    std::map<std::string, Expr*> &valueExprInfo;

    static HelperMapTy createBinOpHelper() {
        HelperMapTy binOpHelper;
        binOpHelper.clear();
        binOpHelper.insert(std::make_pair(BO_Mul, MulOpAF));
        binOpHelper.insert(std::make_pair(BO_Div, DivOpAF));
        binOpHelper.insert(std::make_pair(BO_Rem, DivOpAF));
        binOpHelper.insert(std::make_pair(BO_Add, AddOpAF));
        binOpHelper.insert(std::make_pair(BO_Sub, SubOpAF));
        binOpHelper.insert(std::make_pair(BO_LT, LessOpAF));
        binOpHelper.insert(std::make_pair(BO_GT, GreaterOpAF));
        binOpHelper.insert(std::make_pair(BO_LE, LessOpAF));
        binOpHelper.insert(std::make_pair(BO_GE, GreaterOpAF));
        binOpHelper.insert(std::make_pair(BO_EQ, EqOpAF));
        binOpHelper.insert(std::make_pair(BO_NE, EqOpAF));
        return binOpHelper;
    }

    static HelperMapTy createUOpHelper() {
        HelperMapTy uOpHelper;
        uOpHelper.clear();
        uOpHelper.insert(std::make_pair(UO_PostInc, IncUOpAF));
        uOpHelper.insert(std::make_pair(UO_PostInc, ChangedAF));
        uOpHelper.insert(std::make_pair(UO_PreInc, IncUOpAF));
        uOpHelper.insert(std::make_pair(UO_PreInc, ChangedAF));
        uOpHelper.insert(std::make_pair(UO_PostDec, DecUOpAF));
        uOpHelper.insert(std::make_pair(UO_PostDec, ChangedAF));
        uOpHelper.insert(std::make_pair(UO_PreDec, DecUOpAF));
        uOpHelper.insert(std::make_pair(UO_PreDec, ChangedAF));
        uOpHelper.insert(std::make_pair(UO_AddrOf, AddrOfAF));
        uOpHelper.insert(std::make_pair(UO_Deref, DerefAF));
        uOpHelper.insert(std::make_pair(UO_Minus, SubOpAF));
        return uOpHelper;
    }

    static HelperMapTy createCAOpHelper() {
        HelperMapTy caOpHelper;
        caOpHelper.clear();
        caOpHelper.insert(std::make_pair(BO_MulAssign, MulOpAF));
        caOpHelper.insert(std::make_pair(BO_DivAssign, DivOpAF));
        caOpHelper.insert(std::make_pair(BO_RemAssign, DivOpAF));
        caOpHelper.insert(std::make_pair(BO_AddAssign, AddOpAF));
        caOpHelper.insert(std::make_pair(BO_SubAssign, SubOpAF));
        return caOpHelper;
    }

    void putValueFeature(Expr* v, unsigned int fid) {
        if (v == NULL)
            res[""].insert(fid);
        else {
            Expr *e = stripParenAndCast(v);
            std::string tmp = stmtToString(*ast, e);
            /*if (isIntegerConstant(v)) {
                return;
            }*/
            if (exprContains<BinaryOperator>(v, BO_Assign)) {
                return;
            }
            if (exprContains<CallExpr>(v) && !isAbstractStub(v)) {
                return;
            }
            //if ((tmp == IS_NEG_HANDLER) || (tmp == UNKNOWN_HOOK))
            //    return;
            res[tmp].insert(fid);
            if (valueExprInfo.count(tmp) == 0) {
                valueExprInfo.insert(std::make_pair(tmp, e));
            }
        }
    }

    void putStmtType(Expr* v, Stmt *S) {
        if (llvm::isa<IfStmt>(S)) {
            //if (isReplace)
            //    S->dump();
            //assert(!isReplace);
            if (!isReplace)
                putValueFeature(v, StmtIfAF);
        }
        if (llvm::isa<BinaryOperator>(S)) {
            BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(S);
            if (BO->getOpcode() == BO_Assign)
                putValueFeature(v, isReplace ? RStmtAssignAF : StmtAssignAF);
        }
        if (llvm::isa<CallExpr>(S)) {
            if (isAbstractStub(llvm::dyn_cast<CallExpr>(S)))
                return;
            putValueFeature(v, isReplace ? RStmtCallAF : StmtCallAF);
        }
        if (llvm::isa<WhileStmt>(S) || llvm::isa<ForStmt>(S)) {
            assert(!isReplace);
            putValueFeature(v, StmtLoopAF);
        }
        if (llvm::isa<BreakStmt>(S) || llvm::isa<ReturnStmt>(S) || llvm::isa<GotoStmt>(S))
            putValueFeature(v, isReplace ? RStmtControlAF : StmtControlAF);
        if (llvm::isa<LabelStmt>(S)) {
            assert(!isReplace);
            putValueFeature(v, StmtLabelAF);
        }
    }

public:
    FeatureExtractVisitor(ASTContext *ast, std::map<std::string, Expr*> &valueExprInfo): ast(ast), res(),
        stmtStack(), isReplace(false), abst_v(NULL), is_replace_strconst(false), valueExprInfo(valueExprInfo) { }

    virtual bool VisitBinaryOperatorImpl(BinaryOperator *BO) {
        std::pair<HelperMapTy::const_iterator, HelperMapTy::const_iterator> range =
            binOpHelper.equal_range(BO->getOpcode());
        Expr* LHS = BO->getLHS();
        Expr* RHS = BO->getRHS();
        for (HelperMapTy::const_iterator it = range.first; it != range.second; ++it) {
            putValueFeature(LHS, it->second);
            putValueFeature(RHS, it->second);
        }
        // Assign we only put left hand side
        if (BO->getOpcode() == BO_Assign) {
            putValueFeature(LHS, AssignLHSAF);
            putValueFeature(LHS, ChangedAF);
            if (isZeroValue(RHS))
                putValueFeature(LHS, AssignZeroAF);
            if (isIntegerConstant(RHS))
                putValueFeature(LHS, AssignConstantAF);
        }
        return true;
    }

#define OPERATOR(NAME) \
    virtual bool VisitBin##NAME(BinaryOperator *BO) { \
        return VisitBinaryOperatorImpl(BO); \
    }

    MY_BINOP_LIST()
#undef OPERATOR

    virtual bool VisitUnaryOperatorImpl(UnaryOperator *UO) {
        std::pair<HelperMapTy::const_iterator, HelperMapTy::const_iterator> range =
            uOpHelper.equal_range(UO->getOpcode());
        Expr *subE = UO->getSubExpr();
        for (HelperMapTy::const_iterator it = range.first; it != range.second; ++it)
            putValueFeature(subE, it->second);
        return true;
    }

#define OPERATOR(NAME) \
    virtual bool VisitUnary##NAME(UnaryOperator *UO) { \
        return VisitUnaryOperatorImpl(UO); \
    }

    MY_UNARYOP_LIST()
#undef OPERATOR

    virtual bool VisitCompoundAssignOperatorImpl(CompoundAssignOperator *CAO) {
        std::pair<HelperMapTy::const_iterator, HelperMapTy::const_iterator> range =
            caOpHelper.equal_range(CAO->getOpcode());
        Expr *LHS = CAO->getLHS();
        Expr *RHS = CAO->getRHS();
        for (HelperMapTy::const_iterator it = range.first; it != range.second; ++it) {
            putValueFeature(LHS, it->second);
            putValueFeature(RHS, it->second);
        }
        putValueFeature(LHS, ChangedAF);
        return true;
    }

#define OPERATOR(NAME) \
    virtual bool VisitBin##NAME##Assign(CompoundAssignOperator *CAO) { \
        return VisitCompoundAssignOperatorImpl(CAO); \
    }

    MY_CAO_LIST()
#undef OPERATOR

    virtual bool VisitMemberExpr(MemberExpr *ME) {
        Expr *base = ME->getBase();
        if (ME->isArrow())
            putValueFeature(base, DerefAF);
        putValueFeature(base, MemberAccessAF);
        return true;
    }

    virtual bool VisitCallExpr(CallExpr *CE) {
        Expr *callee = CE->getCallee();
        if (isAbstractStub(CE)) {
            if (abst_v) {
                if (isReplace)
                    putValueFeature(abst_v, RStmtCondAF);
                else
                    putValueFeature(abst_v, StmtIfAF);
            }
            else if (is_replace_strconst) {
                // OK, we are in string const replacement part
                putValueFeature(CE, AbstVAF);
            }
        }
        else
            putValueFeature(callee, CalleeAF);
        for (CallExpr::arg_iterator it = CE->arg_begin(); it != CE->arg_end(); ++it)
            putValueFeature(*it, CallArgumentAF);
        return true;
    }

    virtual bool TraverseStmt(Stmt* S) {
        stmtStack.push_back(S);
        bool propagate = true;
        bool ret = true;
        if (S) {
            putStmtType(NULL, S);
            CallExpr *CE = llvm::dyn_cast<CallExpr>(S);
            if (CE)
                if (isAbstractStub(CE)) {
                    propagate = false;
                    ret = VisitCallExpr(CE);
                    ret &= VisitExpr(CE);
                }
        }
        if (propagate)
            ret = RecursiveASTVisitor::TraverseStmt(S);
        stmtStack.pop_back();
        return ret;
    }

    virtual bool VisitArraySubscriptExpr(ArraySubscriptExpr *ASE) {
        Expr* LHS = ASE->getLHS();
        Expr* RHS = ASE->getRHS();
        putValueFeature(LHS, DerefAF);
        putValueFeature(RHS, IndexAF);
        return true;
    }

    virtual bool VisitExpr(Expr* E) {
        assert( stmtStack.size() > 0 );
        size_t i = stmtStack.size() - 1;
        while (true) {
            if (isAbstractStub(E) && abst_v)
                putStmtType(abst_v, stmtStack[i]);
            else {
                putStmtType(E, stmtStack[i]);
            }
            if (i == 0)
                break;
            if (llvm::isa<IfStmt>(stmtStack[i - 1]))
                break;
            if (llvm::isa<CompoundStmt>(stmtStack[i - 1]))
                break;
            i --;
        }
        return true;
    }

    void TraverseRC(const RepairCandidate &rc, clang::Expr *abst_v) {
        this->abst_v = abst_v;
        if (abst_v != NULL)
            putValueFeature(abst_v, AbstVAF);
        this->is_replace_strconst = (rc.kind == RepairCandidate::ReplaceStringKind);
        assert( rc.actions.size() > 0);
        isReplace = (rc.actions[0].kind == RepairAction::ReplaceMutationKind);
        if ((rc.kind == RepairCandidate::TightenConditionKind) ||
            (rc.kind == RepairCandidate::LoosenConditionKind) ||
            (rc.kind == RepairCandidate::GuardKind) ||
            (rc.kind == RepairCandidate::SpecialGuardKind)) {
            IfStmt *IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
            putValueFeature(NULL, RStmtCondAF);
            Expr* cond = IFS->getCond();
            TraverseStmt(cond);
        }
        else {
            TraverseStmt((Stmt*)rc.actions[0].ast_node);
        }
    }

    ValueToFeatureMapTy getFeatureResult() {
        // FIXME: Going to filter out some messy stuff in NULL stmtTypeFeature
        // We just want one type to dominate here
        FeatureSetTy &tmp = res[""];
        if (tmp.count(StmtLoopAF)) {
            tmp.erase(StmtIfAF);
            tmp.erase(StmtAssignAF);
            tmp.erase(StmtCallAF);
            tmp.erase(StmtControlAF);
            tmp.erase(StmtLabelAF);
        }
        else if (tmp.count(StmtIfAF)) {
            tmp.erase(StmtAssignAF);
            tmp.erase(StmtCallAF);
            tmp.erase(StmtControlAF);
            tmp.erase(StmtLabelAF);
        }
        else if (tmp.count(StmtLabelAF)) {
            tmp.erase(StmtControlAF);
            tmp.erase(StmtAssignAF);
            tmp.erase(StmtCallAF);
        }
        else if (tmp.count(StmtControlAF)) {
            tmp.erase(StmtCallAF);
            tmp.erase(StmtAssignAF);
        }
        else if (tmp.count(StmtAssignAF)) {
            tmp.erase(StmtCallAF);
        }
        return res;
    }
};

const FeatureExtractVisitor::HelperMapTy FeatureExtractVisitor::binOpHelper =
                                            FeatureExtractVisitor::createBinOpHelper();
const FeatureExtractVisitor::HelperMapTy FeatureExtractVisitor::uOpHelper =
                                            FeatureExtractVisitor::createUOpHelper();
const FeatureExtractVisitor::HelperMapTy FeatureExtractVisitor::caOpHelper =
                                            FeatureExtractVisitor::createCAOpHelper();


inline FeatureProductSetTy computeProduct(const FeatureSetTy &s1, const FeatureSetTy &s2) {
    FeatureProductSetTy ret;
    ret.clear();
    for (FeatureSetTy::const_iterator it1 = s1.begin(); it1 != s1.end(); ++it1)
        for (FeatureSetTy::const_iterator it2 = s2.begin(); it2 != s2.end(); ++it2)
            ret.insert(std::make_pair(*it1, *it2));
    return ret;
}

FeatureProductSetTy crossMappingProduct(const ValueToFeatureMapTy &m1, const ValueToFeatureMapTy &m2,
        std::map<std::string, Expr*> &valueExprInfo) {
    FeatureProductSetTy ret;
    ret.clear();
    for (ValueToFeatureMapTy::const_iterator it = m1.begin(); it != m1.end(); ++it) {
        // FIXME: This is hacky, I want to skip integer constant somehow
        if (valueExprInfo.count(it->first)) {
            Expr *E = valueExprInfo[it->first];
            if (isIntegerConstant(E))
                continue;
        }
        ValueToFeatureMapTy::const_iterator it2 = m2.find(it->first);
        if (it2 != m2.end()) {
            FeatureProductSetTy tmp = computeProduct(it->second, it2->second);
            ret.insert(tmp.begin(), tmp.end());
        }
    }
    return ret;
}

const int kind_m[9] = {CondRepair, CondRepair, GuardRepair, GuardRepair,
                    AddControlRepair, AddStmtRepair, ReplaceStmtRepair, ReplaceStmtRepair, AddStmtRepair};

FeatureSetTy extractRepairFeatures(const RepairCandidate &rc) {
    FeatureSetTy ret;
    ret.clear();
    ret.insert(kind_m[rc.kind]);
    return ret;
}

inline void orMap(ValueToFeatureMapTy &m1, const ValueToFeatureMapTy &m2) {
    for (ValueToFeatureMapTy::const_iterator it = m2.begin(); it != m2.end(); ++it)
        m1[it->first].insert(it->second.begin(), it->second.end());
}

FeatureSetTy extractValueFeature(const std::string &v_str, const RepairCandidate &rc,
        SourceContextManager &M, Expr* abst_v, std::map<std::string, Expr*> &valueExprInfo) {
    FeatureSetTy ret;
    ret.clear();
    ASTContext *ast = M.getSourceContext(rc.actions[0].loc.filename);
    LocalAnalyzer *L = M.getLocalAnalyzer(rc.actions[0].loc);
    /*if (abst_v != NULL) {
        std::string abst_v_str = stmtToString(*ast, abst_v);
        if (abst_v_str == v_str)
            ret.insert(AbstCondVF);
    }*/
    if ((rc.oldRExpr != NULL) && (rc.newRExpr != NULL)) {
        std::string old_v_str = stmtToString(*ast, rc.oldRExpr);
        std::string new_v_str = stmtToString(*ast, rc.newRExpr);
        if (v_str == new_v_str)
            ret.insert(ModifiedVF);
        if (old_v_str.size() && new_v_str.size()) {
            double ratio = ((double)old_v_str.size()) / new_v_str.size();
            if (ratio > 0.5 && ratio < 2 && old_v_str.size() > 3 && new_v_str.size() > 3)
                if ((old_v_str.find(new_v_str) != std::string::npos) ||
                    (new_v_str.find(old_v_str) != std::string::npos))
                    ret.insert(ModifiedSimilarVF);
        }
    }
    FunctionDecl *FD = L->getCurrentFunction();
    for (FunctionDecl::param_iterator it = FD->param_begin(); it != FD->param_end(); ++it) {
        ParmVarDecl *VD = *it;
        if (VD->getName() == v_str)
            ret.insert(FuncArgumentVF);
    }
    if (v_str.find("len") != std::string::npos)
        ret.insert(LenLiteralVF);
    assert(valueExprInfo.count(v_str) != 0);
    Expr *E = stripParenAndCast(valueExprInfo[v_str]);
    if (llvm::isa<DeclRefExpr>(E)) {
        DeclRefExpr *DRE = llvm::dyn_cast<DeclRefExpr>(E);
        VarDecl *VD = llvm::dyn_cast<VarDecl>(DRE->getDecl());
        if (VD) {
            if (L->getLocalVarDecls().count(VD))
                ret.insert(LocalVarVF);
            if (L->getGlobalVarDecls().count(VD))
                ret.insert(GlobalVarVF);
        }
    }
    if (exprContains<MemberExpr>(E))
        ret.insert(MemberVF);
    QualType QT = E->getType();
    if (QT->isPointerType() && !isAbstractStub(E)) {
        QualType QT1 = QT->getPointeeType();
        if (!QT1->isFunctionType())
            ret.insert(PointerVF);
        if (QT1->isStructureType())
            ret.insert(StructPointerVF);
    }
    if (llvm::isa<IntegerLiteral>(stripParenAndCast(E))) {
        if (isZeroValue(stripParenAndCast(E))) {
            ret.insert(ZeroConstVF);
        }
        else {
            ret.insert(NonZeroConstVF);
        }
    }
    if (llvm::isa<StringLiteral>(E))
        ret.insert(StringLiteralVF);
    // A special case, this should only happen when doing
    // string const replacement
    if (isAbstractStub(E)) {
        assert(rc.kind == RepairCandidate::ReplaceStringKind);
        ret.insert(ModifiedVF);
        ret.insert(StringLiteralVF);
    }
    return ret;
}

std::vector<Stmt*> getImmediateFollowStmts(const RepairCandidate &rc) {
    std::vector<Stmt*> ret;
    ret.clear();
    ASTLocTy loc = rc.actions[0].loc;
    if (rc.actions[0].kind != RepairAction::ReplaceMutationKind) {
        ret.push_back(loc.stmt);
        return ret;
    }
    else {
        ret.push_back(loc.stmt);
        IfStmt *IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
        Stmt* ElseB = NULL;
        if (IFS) {
            CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(IFS->getThen());
            if (CS) {
                for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it)
                    ret.push_back(*it);
            }
            else
                ret.push_back(IFS->getThen());
            ElseB = IFS->getElse();
            if (ElseB) {
                CS = llvm::dyn_cast<CompoundStmt>(ElseB);
                if (CS)
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it)
                        ret.push_back(*it);
                else
                    ret.push_back(ElseB);
            }
        }
        if (!ElseB) {
            CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(loc.parent_stmt);
            if (CS) {
                bool found = false;
                for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                    if (found) {
                        ret.push_back(*it);
                        break;
                    }
                    if (*it == loc.stmt)
                        found = true;
                }
            }
        }
        return ret;
        /*
        IfStmt *IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
        Stmt *ThenB = NULL;
        Stmt *ElseB = NULL;
        // If this is a if-statement, we are going to get first statement of two branches
        if (IFS) {
            ThenB = IFS->getThen();
            if (ThenB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ThenB);
                if (CS && CS->size() > 0)
                    ret.push_back(*(CS->body_begin()));
                else
                    ret.push_back(ThenB);
            }
            ElseB = IFS->getElse();
            if (ElseB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ElseB);
                if (CS && CS->size() > 0)
                    ret.push_back(*(CS->body_begin()));
                else
                    ret.push_back(ElseB);
            }
        }
        // We are going to consider next in sequence if it does not have else branch
        if (!ElseB) {
            CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(loc.parent_stmt);
            if (CS) {
                bool found = false;
                for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                    if (found) {
                        ret.push_back(*it);
                        break;
                    }
                    if (*it == loc.stmt)
                        found = true;
                }
            }
        }
        return ret;*/
    }
}

#define LOOKUP_DIS 3

void getLocalStmts(const RepairCandidate &rc, std::vector<Stmt*> &ret_before, std::vector<Stmt*> &ret_after) {
    ret_before.clear();
    ret_after.clear();
    ASTLocTy loc = rc.actions[0].loc;
    // Grab all compound stmt that is around the original stmt
    CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(loc.parent_stmt);
    if (CS) {
        std::vector<Stmt*> tmp;
        tmp.clear();
        unsigned long idx = 0;
        bool found = false;
        for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
            if (*it == loc.stmt) {
                found = true;
                idx = tmp.size();
            }
            tmp.push_back(*it);
        }
        assert( found);
        unsigned long s = 0;
        if (idx > LOOKUP_DIS)
            s = idx - LOOKUP_DIS;
        unsigned long e = tmp.size();
        if (idx + LOOKUP_DIS + 1 < tmp.size())
            e = idx + LOOKUP_DIS + 1;
        bool before = true;
        for (size_t i = s; i < e; i++) {
            if (tmp[i] != loc.stmt) {
                if (before)
                    ret_before.push_back(tmp[i]);
                else
                    ret_after.push_back(tmp[i]);
            }
            if (tmp[i] == loc.stmt)
                before = false;
        }
    }
    if (rc.actions[0].kind != RepairAction::ReplaceMutationKind)
        ret_after.push_back(loc.stmt);
/*    if (rc.actions[0].kind == RepairAction::ReplaceMutationKind) {
        IfStmt *IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
        if (IFS) {
            Stmt* ThenB = IFS->getThen();
            if (ThenB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ThenB);
                if (CS) {
                    size_t cnt = 0;
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                        cnt ++;
                        if (cnt > LOOKUP_DIS)
                            break;
                        ret_after.push_back(*it);
                    }
                }
                else
                    ret_after.push_back(ThenB);
            }
            Stmt* ElseB = IFS->getElse();
            if (ElseB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ElseB);
                if (CS) {
                    size_t cnt = 0;
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                        cnt ++;
                        if (cnt > LOOKUP_DIS)
                            break;
                        ret_after.push_back(*it);
                    }
                }
                else
                    ret_after.push_back(ElseB);
            }
        }
    }*/
}

/*
std::vector<Stmt*> getLocalStmts(const RepairCandidate &rc) {
    std::vector<Stmt*> ret;
    ret.clear();
    ASTLocTy loc = rc.actions[0].loc;
    // Grab all compound stmt that is around the original stmt
    CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(loc.parent_stmt);
    if (CS) {
        std::vector<Stmt*> tmp;
        tmp.clear();
        unsigned long idx = 0;
        bool found = false;
        for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
            if (*it == loc.stmt) {
                found = true;
                idx = tmp.size();
            }
            tmp.push_back(*it);
        }
        assert( found);
        unsigned long s = 0;
        if (idx > LOOKUP_DIS)
            s = idx - LOOKUP_DIS;
        unsigned long e = tmp.size();
        if (idx + LOOKUP_DIS + 1 < tmp.size())
            e = idx + LOOKUP_DIS + 1;
        for (size_t i = s; i < e; i++)
            if (tmp[i] != loc.stmt)
                ret.push_back(tmp[i]);
    }
    ret.push_back(loc.stmt);
    if (rc.actions[0].kind == RepairAction::ReplaceMutationKind) {
        IfStmt *IFS = llvm::dyn_cast<IfStmt>((Stmt*)rc.actions[0].ast_node);
        if (IFS) {
            Stmt* ThenB = IFS->getThen();
            if (ThenB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ThenB);
                if (CS) {
                    size_t cnt = 0;
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                        cnt ++;
                        if (cnt > LOOKUP_DIS)
                            break;
                        ret.push_back(*it);
                    }
                }
                else
                    ret.push_back(ThenB);
            }
            Stmt* ElseB = IFS->getElse();
            if (ElseB) {
                CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(ElseB);
                if (CS) {
                    size_t cnt = 0;
                    for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
                        cnt ++;
                        if (cnt > LOOKUP_DIS)
                            break;
                        ret.push_back(*it);
                    }
                }
                else
                    ret.push_back(ElseB);
            }
        }
    }
    return ret;
}*/

/*std::vector<Stmt*> getLocalStmts(const RepairCandidate &rc) {
    std::vector<Stmt*> ret;
    ret.clear();
    ASTLocTy loc = rc.actions[0].loc;
    CompoundStmt *CS = llvm::dyn_cast<CompoundStmt>(loc.parent_stmt);
    if (CS) {
        std::vector<Stmt*> tmp;
        tmp.clear();
        bool found = false;
        unsigned cnt = 0;
        for (CompoundStmt::body_iterator it = CS->body_begin(); it != CS->body_end(); ++it) {
            if (*it == loc.stmt) {
                size_t start = 0;
                if (tmp.size() > LOOKUP_DIS)
                    start = tmp.size() - LOOKUP_DIS;
                for (size_t i = start; i < tmp.size(); i++)
                    ret.push_back(tmp[i]);
                found = true;
                cnt = 0;
            }
            if (found) {
                ret.push_back(*it);
                cnt ++;
                if (cnt > LOOKUP_DIS)
                    break;
            }
            else
                tmp.push_back(*it);
        }
        assert(ret.size() != 0);
        return ret;
    }
    // FIXME: we may miss a lot of stuff, we simply include the parent statement
    // for the non-compound statement case.
    ret.push_back(loc.stmt);
    return ret;
}*/

}

const unsigned int FeatureVector::MAX_FEATURE =
    MAX_REPAIR_FEATURE_KIND + 3 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND +
    3 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND +
    MAX_ATOM_FEATURE_KIND * MAX_VALUE_FEATURE_KIND;

FeatureVector FeatureExtractor::extractFeature(SourceContextManager &M,
        const RepairCandidate &rc, clang::Expr* insVar) {
    std::set<unsigned int> retVec;
    FeatureSetTy res1 = extractRepairFeatures(rc);
    ValueToFeatureMapTy resv, resv_loc, resv_loc1, resv_loc2;

    retVec.clear();
    if (!DisableModificationFeatures.getValue())
        for (FeatureSetTy::iterator it = res1.begin(); it != res1.end(); it++) {
            retVec.insert(*it);
        }

    {
        ASTContext *ast = M.getSourceContext(rc.actions[0].loc.filename);
        FeatureExtractVisitor FEV(ast, valueExprInfo);
        FEV.TraverseRC(rc, insVar);
        resv = FEV.getFeatureResult();
        std::vector<Stmt*> loc_stmts = getImmediateFollowStmts(rc); //getLocalStmts(rc);
        std::vector<Stmt*> loc1_stmts, loc2_stmts; // = getLocalStmts(rc);
        getLocalStmts(rc, loc1_stmts, loc2_stmts);
        resv_loc.clear();
        resv_loc1.clear();
        resv_loc2.clear();
        for (size_t i = 0; i < loc_stmts.size(); i++) {
            if (cache.count(loc_stmts[i]))
                orMap(resv_loc, cache[loc_stmts[i]]);
            else {
                FeatureExtractVisitor FEV(ast, valueExprInfo);
                FEV.TraverseStmt(loc_stmts[i]);
                ValueToFeatureMapTy resM = FEV.getFeatureResult();
                orMap(resv_loc, resM);
                cache[loc_stmts[i]] = resM;
            }
        }
        for (size_t i = 0; i < loc1_stmts.size(); i++) {
            if (cache.count(loc1_stmts[i]))
                orMap(resv_loc1, cache[loc1_stmts[i]]);
            else {
                FeatureExtractVisitor FEV(ast, valueExprInfo);
                FEV.TraverseStmt(loc1_stmts[i]);
                ValueToFeatureMapTy resM = FEV.getFeatureResult();
                orMap(resv_loc1, resM);
                cache[loc1_stmts[i]] = resM;
            }
        }
        for (size_t i = 0; i < loc2_stmts.size(); i++) {
            if (cache.count(loc2_stmts[i]))
                orMap(resv_loc2, cache[loc2_stmts[i]]);
            else {
                FeatureExtractVisitor FEV(ast, valueExprInfo);
                FEV.TraverseStmt(loc2_stmts[i]);
                ValueToFeatureMapTy resM = FEV.getFeatureResult();
                orMap(resv_loc2, resM);
                cache[loc2_stmts[i]] = resM;
            }
        }
    }

    {
        const size_t ATOM_BASE = MAX_REPAIR_FEATURE_KIND;
        if (!DisableModificationFeatures.getValue()) {
            ValueToFeatureMapTy::iterator fit = resv_loc.find("");
            if (fit != resv_loc.end()) {
                FeatureProductSetTy prod = computeProduct(res1, fit->second);
                for (FeatureProductSetTy::iterator it = prod.begin(); it != prod.end(); ++it)
                    retVec.insert(ATOM_BASE + (it->first) * MAX_ATOM_FEATURE_KIND + it->second);
            }
            fit = resv_loc1.find("");
            if (fit != resv_loc1.end()) {
                FeatureProductSetTy prod = computeProduct(res1, fit->second);
                for (FeatureProductSetTy::iterator it = prod.begin(); it != prod.end(); ++it)
                    retVec.insert(ATOM_BASE + MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND + (it->first) * MAX_ATOM_FEATURE_KIND + it->second);
            }
            fit = resv_loc2.find("");
            if (fit != resv_loc2.end()) {
                FeatureProductSetTy prod = computeProduct(res1, fit->second);
                for (FeatureProductSetTy::iterator it = prod.begin(); it != prod.end(); ++it)
                    retVec.insert(ATOM_BASE + 2 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND + (it->first) * MAX_ATOM_FEATURE_KIND + it->second);
            }
        }

        resv.erase("");
        resv_loc.erase("");
        resv_loc1.erase("");
        resv_loc2.erase("");
    }

    {
        const size_t ATOM_V_BASE = MAX_REPAIR_FEATURE_KIND +
            3 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
        if (!DisableSemanticCrossFeatures.getValue()) {
            FeatureProductSetTy tmp;
            tmp = crossMappingProduct(resv, resv_loc, valueExprInfo);
            for (FeatureProductSetTy::iterator it = tmp.begin(); it != tmp.end(); it++)
                retVec.insert(ATOM_V_BASE + it->first * MAX_ATOM_FEATURE_KIND + it->second);
            tmp = crossMappingProduct(resv, resv_loc1, valueExprInfo);
            for (FeatureProductSetTy::iterator it = tmp.begin(); it != tmp.end(); it++)
                retVec.insert(ATOM_V_BASE + MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND + it->first * MAX_ATOM_FEATURE_KIND + it->second);
            tmp = crossMappingProduct(resv, resv_loc2, valueExprInfo);
            for (FeatureProductSetTy::iterator it = tmp.begin(); it != tmp.end(); it++)
                retVec.insert(ATOM_V_BASE + 2 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND + it->first * MAX_ATOM_FEATURE_KIND + it->second);
        }
    }

    {
        const size_t ATOM_V2_BASE = MAX_REPAIR_FEATURE_KIND +
            3 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND +
            3 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
        if (!DisableSemanticValueFeatures.getValue()) {
            for (ValueToFeatureMapTy::iterator it = resv.begin(); it != resv.end(); ++it) {
                FeatureSetTy vset = extractValueFeature(it->first, rc, M, insVar, valueExprInfo);
                FeatureProductSetTy prod = computeProduct(it->second, vset);
                for (FeatureProductSetTy::iterator it2 = prod.begin(); it2 != prod.end(); ++it2)
                    retVec.insert(ATOM_V2_BASE + (it2->first) * MAX_VALUE_FEATURE_KIND + it2->second);
            }
        }
    }

    FeatureVector ret;
    ret.clear();
    ret.insert(ret.begin(), retVec.begin(), retVec.end());
    return ret;
}

std::string FeatureVector::fidToString(unsigned int fid) {
    const unsigned int GLOBAL_FEATURE_BASE = MAX_REPAIR_FEATURE_KIND;
    const unsigned int CROSS_FEATURE_BASE = GLOBAL_FEATURE_BASE +
        3 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
    const unsigned int VALUE_FEATURE_BASE = CROSS_FEATURE_BASE +
        3 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
    std::string ret;
    // this is a repair kind feature
    if (fid < GLOBAL_FEATURE_BASE) {
        ret = repairFidToString(fid % MAX_REPAIR_FEATURE_KIND);
        /*
        if (fid < MAX_REPAIR_FEATURE_KIND)
            ret += " X !is_first";
        else
            ret += " X is_first";
        */
    }
    else if (fid < CROSS_FEATURE_BASE) {
        // this is a global feature
        unsigned int tmp = fid - GLOBAL_FEATURE_BASE;
        if (tmp < MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND) {
            ret = "GLOBAL " + repairFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        }
        else if (tmp < 2 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND) {
            tmp -= MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
            ret = "GLOBAL- " + repairFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        }
        else {
            tmp -= 2 * MAX_REPAIR_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
            ret = "GLOBAL+ " + repairFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        }
    }
    else if (fid < VALUE_FEATURE_BASE) {
        // this is a var cross feature
        unsigned int tmp = fid - CROSS_FEATURE_BASE;
        if (tmp < MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND)
            ret = "VAR " + atomFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        else if (tmp < 2 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND) {
            tmp -= MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
            ret = "VAR- " + atomFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        }
        else {
            tmp -= 2 * MAX_ATOM_FEATURE_KIND * MAX_ATOM_FEATURE_KIND;
            ret = "VAR+ " + atomFidToString(tmp / MAX_ATOM_FEATURE_KIND) + " X " +
                atomFidToString(tmp % MAX_ATOM_FEATURE_KIND);
        }
    }
    else {
        // this is a value cross feature
        unsigned int tmp = fid - VALUE_FEATURE_BASE;
        ret = "VALUE " + atomFidToString(tmp / MAX_VALUE_FEATURE_KIND) + " X " +
            valueFidToString(tmp % MAX_VALUE_FEATURE_KIND);
    }
    return ret;
}
