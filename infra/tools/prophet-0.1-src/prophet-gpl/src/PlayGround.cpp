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
#include "Utils.h"
#include "BenchProgram.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include <iostream>
#include <string>
#include <cstdlib>
#include <set>
#include <vector>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>

// examples for manipulating clang AST
/*int old_main(int argc, char* argv[]) {
    std::string code;
    readCodeToString(argv[1], code);
    std::vector<std::string> Args;
    Args.clear();
    Args.push_back("-v");
    std::unique_ptr<clang::ASTUnit> A1 = clang::tooling::buildASTFromCodeWithArgs(code, Args, argv[1]);
    clang::TranslationUnitDecl *P = A1->getASTContext().getTranslationUnitDecl();
    clang::DeclContext *DC = llvm::dyn_cast<clang::DeclContext>(P);
    clang::FunctionDecl *FC = NULL;
    for (clang::DeclContext::decl_iterator di = DC->decls_begin(); di != DC->decls_end(); ++di) {
        FC = llvm::dyn_cast<clang::FunctionDecl>(*di);
        if (FC) break;
    }
    DC = llvm::dyn_cast<clang::DeclContext>(FC);
    for (clang::DeclContext::decl_iterator di = DC->decls_begin(); di != DC->decls_end(); ++di) {
        (*di)->dump();
    }
    clang::CompoundStmt *CSt = llvm::dyn_cast<clang::CompoundStmt>(FC->getBody());
    clang::Stmt** tmp = new clang::Stmt*[10];
    int cnt = 1;
    for (clang::CompoundStmt::body_iterator bi = CSt->body_begin(); bi != CSt->body_end(); ++bi) {
        if (bi != CSt->body_begin()) {
            tmp[cnt] = *bi;
            cnt ++;
        }
    }
    clang::IfStmt *IFS1 = llvm::dyn_cast<clang::IfStmt>(*(CSt->body_begin()));
    clang::BinaryOperator *BinOp = llvm::dyn_cast<clang::BinaryOperator>(IFS1->getCond());
    clang::ImplicitCastExpr *ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(BinOp->getLHS());
    llvm::errs() << ICE->getCastKindName() << "\n";
    llvm::errs() << ICE->path_size() << "\n";
    clang::Stmt::EmptyShell empty;

    clang::IfStmt *IFS = new(A1->getASTContext()) clang::IfStmt(empty);
    clang::IntegerLiteral *IL = clang::IntegerLiteral::Create(A1->getASTContext(), empty);
    IL->setValueKind(clang::VK_RValue);
    IL->setObjectKind(clang::OK_Ordinary);
    IL->setValue(A1->getASTContext(), llvm::APInt(32, 0));
    IL->setType(A1->getASTContext().IntTy);
    //IFS->setCond(IL);

    clang::ASTContext &Con = A1->getASTContext();
    clang::IdentifierInfo *x = &Con.Idents.get("a");
    clang::DeclarationName dName = clang::DeclarationName(x);
    DC = llvm::dyn_cast<clang::DeclContext>(P);
    clang::DeclContext::lookup_result res = DC->lookup(dName);
    llvm::errs() << "here\n";
    llvm::errs() << res.size() << "\n";
    clang::ValueDecl *vd = llvm::dyn_cast<clang::ValueDecl>(*res.begin());
    llvm::errs() << "here\n";
    clang::DeclRefExpr *DRE = clang::DeclRefExpr::Create(Con,
                                clang::NestedNameSpecifierLoc(),
                                clang::SourceLocation(), vd, false,
                                clang::SourceLocation(), vd->getType(),
                                clang::VK_LValue);
//    clang::DeclRefExpr *DRE = clang::DeclRefExpr::CreateEmpty(Con, false, false, false, 0);
//    DRE->setDecl(vd);
//    DRE->setValueKind(clang::VK_LValue);
//    DRE->setObjectKind(clang::OK_Ordinary);
//    DRE->setType(vd->getType());
    clang::ImplicitCastExpr *myICE = clang::ImplicitCastExpr::CreateEmpty(Con, 0);
    myICE->setSubExpr(DRE);
    myICE->setType(DRE->getType());
    myICE->setCastKind(clang::CK_LValueToRValue);
    myICE->setValueKind(clang::VK_RValue);
    myICE->setObjectKind(clang::OK_Ordinary);
    IFS->setCond(myICE);

    clang::ReturnStmt *Rs = new(A1->getASTContext()) clang::ReturnStmt(clang::Stmt::EmptyShell());
    Rs->setRetValue(IL);
    IFS->setThen(Rs);
    tmp[0] = IFS;
    P->dump();
    P->print(llvm::errs());
    if (FC)
        FC->dump();
    CSt->setStmts(A1->getASTContext(), tmp, cnt);
    P->dump();
    P->print(llvm::errs());
    return 0;
}

int main() {
    printf("Initialize the object...\n");
    BenchProgram P("__tmpmaster", "php-src-tests",*/
//            "./php-build.py", "./php-test.py", "./*.py");
/*    printf("Fetching args for sapi/cli/php_cli.c...\n");
    std::vector<std::string> args;
    std::string build_dir;
    P.getCompileMisc("sapi/cli/php_cli.c", build_dir, args);
    printf("Building the app...\n");
    P.buildFull();
    printf("Finish...\n");
    return 0;
}*/

int main() {
    return 0;
}
