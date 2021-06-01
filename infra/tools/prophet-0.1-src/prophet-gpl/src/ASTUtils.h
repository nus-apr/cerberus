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
#include "ErrorLocalizer.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/Type.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include <string>
#include <map>
#include <set>

// All unary operators.
#define MY_UNARYOP_LIST()                          \
  OPERATOR(PostInc)   OPERATOR(PostDec)         \
  OPERATOR(PreInc)    OPERATOR(PreDec)          \
  OPERATOR(AddrOf)    OPERATOR(Deref)           \
  OPERATOR(Plus)      OPERATOR(Minus)           \
  OPERATOR(Not)       OPERATOR(LNot)            \
  OPERATOR(Real)      OPERATOR(Imag)            \
  OPERATOR(Extension)

// All binary operators (excluding compound assign operators).
#define MY_BINOP_LIST() \
  OPERATOR(PtrMemD)              OPERATOR(PtrMemI)    \
  OPERATOR(Mul)   OPERATOR(Div)  OPERATOR(Rem)        \
  OPERATOR(Add)   OPERATOR(Sub)  OPERATOR(Shl)        \
  OPERATOR(Shr)                                       \
                                                      \
  OPERATOR(LT)    OPERATOR(GT)   OPERATOR(LE)         \
  OPERATOR(GE)    OPERATOR(EQ)   OPERATOR(NE)         \
  OPERATOR(And)   OPERATOR(Xor)  OPERATOR(Or)         \
  OPERATOR(LAnd)  OPERATOR(LOr)                       \
                                                      \
  OPERATOR(Assign)                                    \
  OPERATOR(Comma)

// All compound assign operators.
#define MY_CAO_LIST()                                                      \
  OPERATOR(Mul) OPERATOR(Div) OPERATOR(Rem) OPERATOR(Add) OPERATOR(Sub) \
  OPERATOR(Shl) OPERATOR(Shr) OPERATOR(And) OPERATOR(Or)  OPERATOR(Xor)

namespace clang {
    class CompountStmt;
    class Stmt;
    class Expr;
    class ASTContext;
    class IntegerLiteral;
    class FunctionDecl;
}

class SourceContextManager;

struct ASTLocTy {
    std::string filename;
    std::string src_file;
    clang::Stmt* parent_stmt;
    clang::Stmt* stmt;

    ASTLocTy() { }

    ASTLocTy(const std::string &filename, const std::string &src_file,
            clang::Stmt *parent_stmt, clang::Stmt* stmt)
        : filename(filename), src_file(src_file), parent_stmt(parent_stmt),
        stmt(stmt) { }

    bool operator < (const ASTLocTy &a) const {
        if (filename != a.filename)
            return filename < a.filename;
        else if (parent_stmt != a.parent_stmt)
            return parent_stmt < a.parent_stmt;
        else
            return stmt < a.stmt;
    }

    std::string toString(SourceContextManager &M) const ;
};

class StmtReplacerImpl;

class StmtReplacer {
    class StmtReplacerImpl *impl;
public:
    StmtReplacer(clang::ASTContext *ctxt, clang::Stmt* S);

    ~StmtReplacer();

    void addRule(clang::Expr* a, clang::Expr *b);

    clang::Stmt* getResult();
};

clang::Stmt* duplicateStmt(clang::ASTContext *ctxt, clang::Stmt* S);

std::map<SourcePositionTy, clang::Stmt*> findCorrespondingStmt(BenchProgram &P, clang::ASTContext *ctxt,
        const std::string &file, const std::set<SourcePositionTy> &locs);

bool typeMatch(clang::QualType Ta, clang::QualType Tb);

bool isZeroValue(clang::Expr *);

size_t getExpLineNumber(clang::ASTContext &C, clang::Stmt *);

bool isIntegerConstant(clang::Expr *);

bool evalIntegerConstant(clang::Expr *, long long &v);

std::string stmtToString(clang::ASTContext &C, clang::Stmt* S);

bool isSameStmt(clang::ASTContext &C, clang::Stmt* S1, clang::Stmt* S2);

clang::CompoundStmt* wrapStmtWithCompoundStmt(clang::ASTContext &C, clang::Stmt*S);

bool isSimpleExpr(clang::Expr *);

clang::IntegerLiteral *getNewIntegerLiteral(clang::ASTContext *ctxt, uint64_t v);

clang::Expr* getParenExpr(clang::ASTContext *ctxt, clang::Expr *E);

clang::Expr* stripParenAndCast(clang::Expr *E);

template<typename T>
class ExprContainsImplVisitor : public clang::RecursiveASTVisitor<ExprContainsImplVisitor<T> > {
    bool res;
    bool check_op;
    unsigned int op;
public:
    ExprContainsImplVisitor() : res(false), check_op(false), op(0) { }

    void checkOp(unsigned int op) {
        this->check_op = true;
        this->op = op;
    }

    bool VisitStmt(clang::Stmt* S) {
        if (S)
            if (llvm::isa<T>(S)) {
                if (!check_op)
                    res = true;
                else {
                    if (llvm::isa<clang::BinaryOperator>(S)) {
                        clang::BinaryOperator *BO = llvm::dyn_cast<clang::BinaryOperator>(S);
                        res = ( BO->getOpcode() == op );
                    }
                    else if (llvm::isa<clang::UnaryOperator>(S)) {
                        clang::UnaryOperator *UO = llvm::dyn_cast<clang::UnaryOperator>(S);
                        res = ( UO->getOpcode() == op );
                    }
                }
            }
        return true;
    }

    bool getResult() {
        return res;
    }
};

template<typename T>
bool exprContains(clang::Expr *E, int op = -1) {
    ExprContainsImplVisitor<T> V;
    if (op >= 0)
        V.checkOp(op);
    V.TraverseStmt(E);
    return V.getResult();
}

bool isYaccFunc(clang::FunctionDecl *FD);
