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
#include "ASTDiffer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include <stdio.h>

using namespace clang;

typedef ASTDiffer::ASTDifferRecord ASTDifferRecord;
typedef ASTDiffer::DiffResultInternalEntry DiffResultInternalEntry;

namespace {

class ASTDifferVisitor : public RecursiveASTVisitor<ASTDifferVisitor> {
public:
    explicit ASTDifferVisitor(ASTContext *Context, std::vector<ASTDifferRecord> *TraverseRecords)
        : Context(Context), TraverseRecords(TraverseRecords) {}

    virtual ~ASTDifferVisitor() {}

    virtual bool TraverseDecl(Decl *n) {
        size_t idx = TraverseRecords->size();
        ASTDifferRecord tmp;
        tmp.NodeKind = ASTDiffer::DeclKind;
        tmp.U.decl = n;
        TraverseRecords->push_back(tmp);
        bool ret = RecursiveASTVisitor<ASTDifferVisitor>::TraverseDecl(n);
        (*TraverseRecords)[idx].end_index = TraverseRecords->size();
        return ret;
    }

    virtual bool TraverseStmt(Stmt *n) {
        size_t idx = TraverseRecords->size();
        ASTDifferRecord tmp;
        tmp.NodeKind = ASTDiffer::StmtKind;
        tmp.U.stmt = n;
        TraverseRecords->push_back(tmp);
        bool ret;
        if (!n || !llvm::isa<BinaryOperator>(n))
            ret = RecursiveASTVisitor<ASTDifferVisitor>::TraverseStmt(n);
        else {
            BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(n);
            ret = TraverseStmt(BO->getLHS());
            ret &= TraverseStmt(BO->getRHS());
        }
        (*TraverseRecords)[idx].end_index = TraverseRecords->size();
        return ret;
    }

    void clearRecords() {
        TraverseRecords->clear();
    }

private:
    ASTContext *Context;
    std::vector<ASTDifferRecord> *TraverseRecords;
};

class ASTDifferConsumer : public clang::ASTConsumer {
public:
    explicit ASTDifferConsumer(ASTContext *Context, std::vector<ASTDifferRecord> *TraverseRecords)
        : Visitor(Context, TraverseRecords) {}

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        Visitor.clearRecords();
        Visitor.TraverseDecl(Context.getTranslationUnitDecl());
    }
private:
    ASTDifferVisitor Visitor;
};

class ASTDifferAction : public clang::ASTFrontendAction {
public:

    ASTDifferAction(std::vector<ASTDifferRecord> *TraverseRecords)
        : TraverseRecords(TraverseRecords) { }

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
        clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        return std::unique_ptr<ASTConsumer>(new ASTDifferConsumer(&Compiler.getASTContext(), TraverseRecords));
    }

private:
    std::vector<ASTDifferRecord> *TraverseRecords;
};

bool readCode(const std::string file, std::string &code) {
    FILE* f = fopen(file.c_str(), "r");
    if (f == NULL)
        return false;
    char tmp[1024];
    int ret;
    code = "";
    while ((ret = fread(tmp, 1, 1000, f)) != 0) {
        tmp[ret] = 0;
        code += tmp;
    }
    fclose(f);
    return true;
}

inline static bool IsSingleNode(size_t idx, std::vector<ASTDifferRecord> &r) {
    return (r[idx].end_index - idx) == 1;
}

inline static bool isSameType(ASTContext *ast1, QualType T1, ASTContext *ast2, QualType T2) {
    if (T1.isNull() && T2.isNull())
        return true;
    if (T1.isNull() || T2.isNull())
        return false;
    std::string tmp1, tmp2;
    llvm::raw_string_ostream sout1(tmp1), sout2(tmp2);
    T1.print(sout1, ast1->getPrintingPolicy());
    T2.print(sout2, ast2->getPrintingPolicy());
    tmp1 = sout1.str();
    tmp2 = sout2.str();
    // XXX: For now, we just completely ignore anonymous type,
    // the correct way would be to compare them carefully
    if (tmp1.find("anonymous ") != std::string::npos && tmp2.find("anonymous ") != std::string::npos)
        return true;
    return tmp1 == tmp2;
}

bool IsSameNode(ASTContext *ast1, ASTContext *ast2, size_t idx1,
        size_t idx2, std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2) {
    if (r1[idx1].NodeKind != r2[idx2].NodeKind)
        return false;
    if (r1[idx1].NodeKind == ASTDiffer::DeclKind) {
        Decl* d1 = r1[idx1].U.decl;
        Decl* d2 = r2[idx2].U.decl;
        //llvm::errs() << d1->getKind() << " v.s. " << d2->getKind() << "\n";
        if (d1->getKind() != d2->getKind())
            return false;
        if (llvm::isa<VarDecl>(d1)) {
            VarDecl *vd1 = llvm::dyn_cast<VarDecl>(d1);
            VarDecl *vd2 = llvm::dyn_cast<VarDecl>(d2);
            if (vd1->getName() != vd2->getName())
                return false;
            QualType QT1 = vd1->getType();
            QualType QT2 = vd2->getType();
            return isSameType(ast1, QT1, ast2, QT2);
        }
        if (llvm::isa<FunctionDecl>(d1)) {
            // TODO: We actually need to compare the full signature, but whatever
            FunctionDecl *fd1 = llvm::dyn_cast<FunctionDecl>(d1);
            FunctionDecl *fd2 = llvm::dyn_cast<FunctionDecl>(d2);
            //return fd1->getDeclName() == fd2->getDeclName();
            return fd1->getName() == fd2->getName();
        }
        return d1->getKind() == d2->getKind();
    }
    else {
        Stmt* s1 = r1[idx1].U.stmt;
        Stmt* s2 = r2[idx2].U.stmt;
        if (s1 == NULL || s2 == NULL)
            return s1 == s2;
        if (s1->getStmtClass() != s2->getStmtClass())
            return false;
        if (llvm::isa<DeclRefExpr>(s1)) {
            DeclRefExpr *e1 = llvm::dyn_cast<DeclRefExpr>(s1);
            DeclRefExpr *e2 = llvm::dyn_cast<DeclRefExpr>(s2);
            if (e1->getDecl()->getKind() != e2->getDecl()->getKind())
                return false;
            if (llvm::isa<ValueDecl>(e1->getDecl()) && llvm::isa<ValueDecl>(e2->getDecl())) {
                ValueDecl *v1 = llvm::dyn_cast<ValueDecl>(e1->getDecl());
                ValueDecl *v2 = llvm::dyn_cast<ValueDecl>(e2->getDecl());
                return v1->getName() == v2->getName();
            }
            return true;
        }
        else if (llvm::isa<MemberExpr>(s1)) {
            MemberExpr *m1 = llvm::dyn_cast<MemberExpr>(s1);
            MemberExpr *m2 = llvm::dyn_cast<MemberExpr>(s2);
            if (m1->isArrow() != m2->isArrow())
                return false;
            return m1->getMemberDecl()->getName() == m2->getMemberDecl()->getName();
        }
        else if (llvm::isa<IntegerLiteral>(s1)) {
            IntegerLiteral *i1 = llvm::dyn_cast<IntegerLiteral>(s1);
            IntegerLiteral *i2 = llvm::dyn_cast<IntegerLiteral>(s2);
            // If they are in different bitwidth, then they are not equal
            if (i1->getValue().getBitWidth() != i2->getValue().getBitWidth())
                return false;
            else
                return i1->getValue() == i2->getValue();
        }
        else if (llvm::isa<StringLiteral>(s1)) {
            StringLiteral *st1 = llvm::dyn_cast<StringLiteral>(s1);
            StringLiteral *st2 = llvm::dyn_cast<StringLiteral>(s2);
            if ((st1->getBytes().endswith(".c") && st2->getBytes().endswith(".c")) ||
                (st1->getBytes().endswith(".h") && st2->getBytes().endswith(".h")))
                return true;
            return st1->getBytes() == st2->getBytes();
        }
        else if (llvm::isa<BinaryOperator>(s1)) {
            BinaryOperator *bo1 = llvm::dyn_cast<BinaryOperator>(s1);
            BinaryOperator *bo2 = llvm::dyn_cast<BinaryOperator>(s2);
            return bo1->getOpcode() == bo2->getOpcode();
        }
        else if (llvm::isa<UnaryOperator>(s1)) {
            UnaryOperator *uo1 = llvm::dyn_cast<UnaryOperator>(s1);
            UnaryOperator *uo2 = llvm::dyn_cast<UnaryOperator>(s2);
            return uo1->getOpcode() == uo2->getOpcode();
        }
        //llvm::errs() << s1->getStmtClassName() << " v.s." << s2->getStmtClassName() << "\n";
        return true;
    }
}

DiffResultEntry ReplacePair(size_t idx1, size_t idx2, std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2) {
    DiffResultEntry ret;
    ret.NodeKind1 = r1[idx1].NodeKind;
    if (ret.NodeKind1 == ASTDiffer::StmtKind)
        ret.Node1.stmt = r1[idx1].U.stmt;
    else
        ret.Node1.decl = r1[idx1].U.decl;
    ret.NodeKind2 = r2[idx2].NodeKind;
    if (ret.NodeKind2 == ASTDiffer::StmtKind)
        ret.Node2.stmt = r2[idx2].U.stmt;
    else
        ret.Node2.decl = r2[idx2].U.decl;
    ret.DiffActionKind = ASTDiffer::ReplaceAction;
    return ret;
}

DiffResultEntry InsertPair(size_t idx1, size_t idx2, std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2) {
    DiffResultEntry ret;
    ret.NodeKind1 = r1[idx1].NodeKind;
    if (ret.NodeKind1 == ASTDiffer::StmtKind)
        ret.Node1.stmt = r1[idx1].U.stmt;
    else
        ret.Node1.decl = r1[idx1].U.decl;
    ret.NodeKind2 = r2[idx2].NodeKind;
    if (ret.NodeKind2 == ASTDiffer::StmtKind)
        ret.Node2.stmt = r2[idx2].U.stmt;
    else
        ret.Node2.decl = r2[idx2].U.decl;
    ret.DiffActionKind = ASTDiffer::InsertAction;
    return ret;
}

DiffResultEntry DeletePair(size_t idx1, size_t idx2, std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2) {
    DiffResultEntry ret;
    ret.NodeKind1 = r1[idx1].NodeKind;
    if (ret.NodeKind1 == ASTDiffer::StmtKind)
        ret.Node1.stmt = r1[idx1].U.stmt;
    else
        ret.Node1.decl = r1[idx1].U.decl;
    ret.NodeKind2 = r2[idx2].NodeKind;
    if (ret.NodeKind2 == ASTDiffer::StmtKind)
        ret.Node2.stmt = r2[idx2].U.stmt;
    else
        ret.Node2.decl = r2[idx2].U.decl;
    ret.DiffActionKind = ASTDiffer::DeleteAction;
    return ret;
}

std::vector<unsigned int> GetChildren(unsigned int idx, std::vector<ASTDifferRecord> &r) {
    std::vector<unsigned int> ret;
    ret.clear();
    unsigned int i = idx + 1;
    unsigned int end = r[idx].end_index;
    while (i < end) {
        ret.push_back(i);
        i = r[i].end_index;
    }
    return ret;
}

void FindParentId(unsigned int idx, std::vector<unsigned int> &p, std::vector<ASTDifferRecord> &r) {
    std::vector<unsigned int> children = GetChildren(idx, r);
    for (size_t i = 0; i < children.size(); i++) {
        p[children[i]] = idx;
        FindParentId(children[i], p, r);
    }
}

std::map<std::pair<unsigned int, unsigned int>, unsigned int> DfsDiffCache;
std::map<std::pair<unsigned int, unsigned int>, std::vector<DiffResultInternalEntry> > DfsDiffResultCache;

bool IsIdentical(ASTContext *ast1, ASTContext *ast2, unsigned int idx1,
        unsigned int idx2, std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2) {
    unsigned int idx1_end = r1[idx1].end_index;
    unsigned int idx2_end = r2[idx2].end_index;
    if ((idx1_end - idx1) != (idx2_end - idx2))
        return false;

    // XXX: I want just to get rid of all source name and line number shit
    if ((r1[idx1].NodeKind == ASTDiffer::StmtKind) && (r2[idx2].NodeKind == ASTDiffer::StmtKind)) {
        Stmt *S1 = r1[idx1].U.stmt;
        Stmt *S2 = r2[idx2].U.stmt;
        if (S1 && S2) {
            CallExpr *CE1 = llvm::dyn_cast<CallExpr>(S1);
            CallExpr *CE2 = llvm::dyn_cast<CallExpr>(S2);
            if (CE1 && CE2) {
                FunctionDecl *FD1 = CE1->getDirectCallee();
                FunctionDecl *FD2 = CE2->getDirectCallee();
                if (FD1 && FD2)
                    if ((FD1->getName() == FD2->getName()) && ((FD1->getName() == "php_info_print_table_row") ||
                                FD1->getName().startswith("ap_log")))
                        return true;
            }
        }
    }

    unsigned i = idx1;
    unsigned j = idx2;
    while (i != idx1_end) {
        if (!IsSameNode(ast1, ast2, i, j, r1, r2))
            return false;
        i ++;
        j ++;
    }
    return true;
}

unsigned int DfsDiff(ASTContext *ast1, ASTContext *ast2, unsigned int idx1, unsigned int idx2,
        std::vector<ASTDifferRecord> &r1, std::vector<ASTDifferRecord> &r2, std::vector<DiffResultInternalEntry> &ret) {
    if (DfsDiffCache.count(std::make_pair(idx1, idx2)) != 0) {
        ret = DfsDiffResultCache[std::make_pair(idx1, idx2)];
        return DfsDiffCache[std::make_pair(idx1, idx2)];
    }

    if (IsIdentical(ast1, ast2, idx1, idx2, r1, r2)) {
        ret.clear();
        return 0;
    }

    if (IsSingleNode(idx1, r1) && IsSingleNode(idx2, r2)) {
        if (IsSameNode(ast1, ast2, idx1, idx2, r1, r2)) {
            ret.clear();
            return 0;
        }
        else {
            ret.clear();
            DiffResultInternalEntry entry = DiffResultInternalEntry(idx1, idx2, ASTDiffer::ReplaceAction);
            ret.push_back(entry);
            return 1;
        }
    }

    if (IsSingleNode(idx1, r1) != IsSingleNode(idx2, r2)) {
        ret.clear();
        DiffResultInternalEntry entry = DiffResultInternalEntry(idx1, idx2, ASTDiffer::ReplaceAction);
        ret.push_back(entry);
        if (r1[idx1].end_index - idx1 > r2[idx2].end_index - idx2)
            return r1[idx1].end_index - idx1;
        else
            return r2[idx2].end_index - idx2;
    }

    if (!IsSameNode(ast1, ast2, idx1, idx2, r1, r2)) {
        ret.clear();
        DiffResultInternalEntry entry = DiffResultInternalEntry(idx1, idx2, ASTDiffer::ReplaceAction);
        ret.push_back(entry);
        if (r1[idx1].end_index - idx1 > r2[idx2].end_index - idx2)
            return r1[idx1].end_index - idx1;
        else
            return r2[idx2].end_index - idx2;
    }

#define IDX(i,j) (((i) << 13) | (j))

    std::vector<unsigned int> children1, children2, tmpc1, tmpc2;
    tmpc1 = GetChildren(idx1, r1);
    tmpc2 = GetChildren(idx2, r2);

    // We are going to shrink huge node list
    {
        size_t i1, j1, i2, j2;
        i1 = j1 = 0;
        while (i1 < tmpc1.size() && j1 < tmpc2.size() && IsIdentical(ast1, ast2, tmpc1[i1], tmpc2[j1], r1, r2)) {
            i1++;
            j1++;
        }
        i2 = tmpc1.size();
        j2 = tmpc2.size();
        while (i2 > i1 && j2 > j1 && IsIdentical(ast1, ast2, tmpc1[i2-1], tmpc2[j2-1], r1, r2)) {
            i2 --;
            j2 --;
        }
        size_t gap = 3;
        if (i1 < gap) gap = i1;
        if (j1 < gap) gap = j1;
        i1 -= gap;
        j1 -= gap;
        i2 += 3;
        j2 += 3;
        if (i2 > tmpc1.size()) {
            j2 -= i2 - tmpc1.size();
            i2 = tmpc1.size();
        }
        if (j2 > tmpc2.size()) {
            i2 -= j2 - tmpc2.size();
            j2 = tmpc2.size();
        }
        children1.clear();
        children2.clear();
        for (size_t i = i1; i < i2; i++) children1.push_back(tmpc1[i]);
        for (size_t i = j1; i < j2; i++) children2.push_back(tmpc2[i]);
    }

    unsigned long n = children1.size();
    unsigned long m = children2.size();
    assert( n <= 8000 );
    assert( m <= 8000 );
    unsigned int *f, *p;
    f = new unsigned int[8192 * 8192];
    p = new unsigned int[8192 * 8192];
    f[0] = 0;
    p[0] = 0;
    for (size_t i = 0; i <= n; i++)
        for (size_t j = 0; j <= m; j++) {
            if (i == 0 && j == 0) continue;
            unsigned int v1, v2, v3;
            std::vector<DiffResultInternalEntry> sub_ret;
            if (i != 0 && j != 0) {
                v1 = DfsDiff(ast1, ast2, children1[i-1], children2[j-1], r1, r2, sub_ret);
                v1 += f[IDX(i-1, j-1)];
            }
            else
                v1 = 0x7FFFF;
            if (i != 0)
                v2 = f[IDX(i-1, j)] + (r1[children1[i - 1]].end_index - children1[i - 1]);
            else
                v2 = 0x7FFFF;
            if (j != 0)
                v3 = f[IDX(i, j-1)] + (r2[children2[j - 1]].end_index - children2[j - 1]);
            else
                v3 = 0x7FFFF;
            if (v1 < v2 && v1 < v3) {
                f[IDX(i, j)] = v1;
                p[IDX(i, j)] = 1;
            }
            else if (v2 < v3) {
                f[IDX(i, j)] = v2;
                p[IDX(i, j)] = 2;
            }
            else {
                f[IDX(i, j)] = v3;
                p[IDX(i, j)] = 3;
            }
        }

    unsigned long i = n;
    unsigned long j = m;
    ret.clear();

    while ((i != 0) || (j != 0)) {
        unsigned int pa = p[IDX(i,j)];
        if (pa == 1) {
            std::vector<DiffResultInternalEntry> sub_res;
            DfsDiff(ast1, ast2, children1[i - 1], children2[j - 1], r1, r2, sub_res);
            ret.insert(ret.end(), sub_res.begin(), sub_res.end());
            i --; j --;
        }
        else if (pa == 2) {
            if (j != m)
                ret.push_back(DiffResultInternalEntry(children1[i-1], children2[j], ASTDiffer::DeleteAction));
            else
                ret.push_back(DiffResultInternalEntry(children1[i - 1], children2[j-1], ASTDiffer::DeleteAction));
            i --;
        }
        else {
            if (i != n)
                ret.push_back(DiffResultInternalEntry(children1[i], children2[j-1], ASTDiffer::InsertAction));
            else
                ret.push_back(DiffResultInternalEntry(children1[i-1], children2[j-1], ASTDiffer::InsertAction));
            j --;
        }
    }

    unsigned int ret_diff = f[IDX(n, m)];
    DfsDiffCache[std::make_pair(idx1, idx2)] = ret_diff;
    DfsDiffResultCache[std::make_pair(idx1, idx2)] = ret;

#undef IDX

    delete[] f;
    delete[] p;

    return ret_diff;
}

}

ASTDiffer::ASTDiffer(ASTContext *ast1, ASTContext *ast2): ast1(ast1), ast2(ast2) { }

bool ASTDiffer::Diff() {
    // NOTE: One thing to note is that buildASTFromCodeWithArgs will not copy the code
    // text to another memory buffer. It instead will use the supplied string buffer
    // and create pointer to point to the buffer (codea/codeb). We need to make sure
    // the buffer is still alive before we move on.
    // llvm::errs() << "Traversing first tree..." << "\n";
    ASTDifferVisitor *visitor1 = new ASTDifferVisitor(ast1, &r1);
    visitor1->TraverseDecl(ast1->getTranslationUnitDecl());
    delete visitor1;
    if (r1.size() <= 0) {
        llvm::errs() << "Cannot traverse the first code!\n";
        return false;
    }
    // llvm::errs() << "Traversing second tree..." << "\n";

    ASTDifferVisitor *visitor2 = new ASTDifferVisitor(ast2, &r2);
    visitor2->TraverseDecl(ast2->getTranslationUnitDecl());
    delete visitor2;
    if (r2.size() <= 0) {
        llvm::errs() << "Cannot traverse the second code!\n";
        return false;
    }

    // llvm::errs() << "Diffing..." << "\n";
    DfsDiffCache.clear();
    DfsDiffResultCache.clear();
    diffDistance = DfsDiff(ast1, ast2, 0, 0, r1, r2, diffRes);
    DfsDiffCache.clear();
    DfsDiffResultCache.clear();

    parent_id1.resize(r1.size());
    parent_id2.resize(r2.size());
    parent_id1[0] = 0;
    parent_id2[0] = 0;
    FindParentId(0, parent_id1, r1);
    FindParentId(0, parent_id2, r2);

    return true;
}

unsigned int ASTDiffer::GetDiffResult(std::vector<DiffResultEntry> &res) {
    res.clear();
    for (size_t i = 0; i < diffRes.size(); i++) {
        if (diffRes[i].kind == ReplaceAction)
            res.push_back(ReplacePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else if (diffRes[i].kind == InsertAction)
            res.push_back(InsertPair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else {
            res.push_back(DeletePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        }
    }
    return diffDistance;
}

bool IsIfStmt(const ASTDifferRecord &rec) {
    if (rec.NodeKind == ASTDiffer::DeclKind) return false;
    if (rec.U.stmt == NULL) return false;
    return llvm::isa<IfStmt>(rec.U.stmt);
}

bool IsCompoundStmt(const ASTDifferRecord &rec) {
    if (rec.NodeKind == ASTDiffer::DeclKind) return false;
    if (rec.U.stmt == NULL) return false;
    return llvm::isa<CompoundStmt>(rec.U.stmt);

}

static bool isDummy(Stmt* S1, Stmt* S2) {
    if (S1 == NULL || S2 == NULL)
        return false;
    CallExpr *CE1 = llvm::dyn_cast<CallExpr>(S1);
    CallExpr *CE2 = llvm::dyn_cast<CallExpr>(S2);
    if (CE1 && CE2) {
        FunctionDecl *FD1 = CE1->getDirectCallee();
        FunctionDecl *FD2 = CE2->getDirectCallee();
        if (FD1 && FD2)
            if ((FD1->getName() == FD2->getName()) && ((FD1->getName() == "php_info_print_table_row") ||
                        FD1->getName().startswith("ap_log")))
                return true;
    }
    return false;
}

static bool isDummy(Decl *D1, Decl *D2) {
    return false;
}

unsigned int ASTDiffer::GetDiffResultForStmt(std::vector<DiffResultEntry> &res) {
    res.clear();
    std::set<std::pair<unsigned int, unsigned int> > tmp;
    tmp.clear();
    for (size_t i = 0; i < diffRes.size(); i++) {
        if (diffRes[i].kind == ASTDiffer::InsertAction)
            res.push_back(InsertPair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else if (diffRes[i].kind == ASTDiffer::DeleteAction)
            res.push_back(DeletePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else if (r1[diffRes[i].idx1].NodeKind == ASTDiffer::DeclKind) {
            if (!isDummy(r1[diffRes[i].idx1].U.decl, r2[diffRes[i].idx2].U.decl))
                res.push_back(ReplacePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        }
        else {
            unsigned int idx1 = diffRes[i].idx1;
            unsigned int idx2 = diffRes[i].idx2;
            unsigned int last_idx1 = idx1;
            unsigned int last_idx2 = idx2;
            while (!IsIfStmt(r1[idx1]) && !IsCompoundStmt(r1[idx1]) && idx1 != 0) {
                last_idx1 = idx1;
                last_idx2 = idx2;
                idx1 = parent_id1[idx1];
                idx2 = parent_id2[idx2];
            }
            bool lift = false;
            if (IsIfStmt(r1[idx1])) {
                IfStmt *IFS = llvm::dyn_cast<IfStmt>(r1[idx1].U.stmt);
                if (IFS->getCond() == r1[last_idx1].U.stmt)
                    lift = true;
            }
            if (lift)
                tmp.insert(std::make_pair(idx1, idx2));
            else
                tmp.insert(std::make_pair(last_idx1, last_idx2));
        }
    }
    for (std::set<std::pair<unsigned int, unsigned int> >::iterator it = tmp.begin();
            it != tmp.end(); ++it) {
        Stmt* S1 = r1[it->first].U.stmt;
        Stmt* S2 = r2[it->second].U.stmt;
        if (!isDummy(S1, S2))
            res.push_back(ReplacePair(it->first, it->second, r1, r2));
    }
    return diffDistance;
}

unsigned int ASTDiffer::GetDiffResultForCond(std::vector<DiffResultEntry> &res) {
    res.clear();
    std::set<std::pair<unsigned int, unsigned int> > tmp;
    tmp.clear();
    for (size_t i = 0; i < diffRes.size(); i++) {
        if (diffRes[i].kind == ASTDiffer::InsertAction)
            res.push_back(InsertPair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else if (diffRes[i].kind == ASTDiffer::DeleteAction)
            res.push_back(DeletePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else if (r1[diffRes[i].idx1].NodeKind == ASTDiffer::DeclKind)
            res.push_back(ReplacePair(diffRes[i].idx1, diffRes[i].idx2, r1, r2));
        else {
            unsigned int idx1 = diffRes[i].idx1;
            unsigned int idx2 = diffRes[i].idx2;
            unsigned int last_idx1 = idx1;
            unsigned int last_idx2 = idx2;
            while (!IsIfStmt(r1[idx1]) && !IsCompoundStmt(r1[idx1]) && idx1 != 0) {
                if (r1[idx1].NodeKind == StmtKind) {
                    /*llvm::errs() << "check! " << idx1 << "\n";
                    r1[idx1].U.stmt->dump();
                    std::vector<unsigned int> tmp = GetChildren(idx1, r1);
                    llvm::errs() << "children size: " << tmp.size() << "\n";
                    for (size_t i = 0; i < tmp.size(); i++) {
                        llvm::errs() << tmp[i] << "\n";
                        r1[tmp[i]].U.stmt->dump();
                    }*/
                    if (llvm::isa<BinaryOperator>(r1[idx1].U.stmt)) {
                        BinaryOperator *BO = llvm::dyn_cast<BinaryOperator>(r1[idx1].U.stmt);
                        if ((BO->getOpcode() == BO_LAnd) || (BO->getOpcode() == BO_LOr)) {
                            //llvm::errs() << "break\n";
                            break;
                        }
                    }
                }
                last_idx1 = idx1;
                last_idx2 = idx2;
                idx1 = parent_id1[idx1];
                idx2 = parent_id2[idx2];
            }
            tmp.insert(std::make_pair(last_idx1, last_idx2));
        }
    }
    for (std::set<std::pair<unsigned int, unsigned int> >::iterator it = tmp.begin();
            it != tmp.end(); ++it) {
        Stmt* S1 = r1[it->first].U.stmt;
        Stmt* S2 = r2[it->second].U.stmt;
        if (!isDummy(S1, S2))
            res.push_back(ReplacePair(it->first, it->second, r1, r2));
    }
    return diffDistance;
}

bool ASTDiffer::InSearchSpaceHelper() {
    for (size_t i = 0; i < diffRes.size(); i++)
        if (diffRes[i].kind == ASTDiffer::ReplaceAction)
            if (r1[diffRes[i].idx1].NodeKind == ASTDiffer::StmtKind) {
                unsigned int idx1 = diffRes[i].idx1;
                unsigned int idx2 = diffRes[i].idx2;
                bool incall = false;
                while (!IsIfStmt(r1[idx1]) && !IsCompoundStmt(r1[idx1]) && idx1 != 0) {
                    idx1 = parent_id1[idx1];
                    idx2 = parent_id2[idx2];
                    if (r1[idx1].NodeKind == StmtKind) {
                        if (llvm::isa<CallExpr>(r1[idx1].U.stmt))
                            incall = true;
                    }
                }
                if (IsIfStmt(r1[idx1]) && incall)
                    return false;
            }
    return true;
}
