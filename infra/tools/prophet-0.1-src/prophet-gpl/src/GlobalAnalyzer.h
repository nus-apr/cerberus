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
#include <map>
#include <set>
#include <string>
#include <vector>

namespace clang {
    class ASTContext;
    class Stmt;
    class Expr;
    class VarDecl;
    class FunctionDecl;
    class EnumConstantDecl;
    class EnumDecl;
}

class GlobalAnalyzer {
    clang::ASTContext &C;
    std::string filename;
    std::set<clang::VarDecl*> GlobalVarDecls;
    std::set<clang::FunctionDecl*> FuncDecls;
    std::map<clang::EnumConstantDecl*, clang::EnumDecl*> EnumMap;
    std::set<clang::Expr*> CandidateExprs;
    std::set<clang::Stmt*> CandidateMacroExps;
    std::set<clang::Stmt*> CandidateIfStmts;

public:

    typedef std::vector<clang::Expr*> ExprListTy;

    GlobalAnalyzer(clang::ASTContext &C, const std::string &filename);

    const std::set<clang::FunctionDecl*> & getFuncDecls() {
        return FuncDecls;
    }

    const std::set<clang::VarDecl*> & getGlobalVarDecls() {
        return GlobalVarDecls;
    }

    const std::set<clang::Expr*> & getCandidateExprs() {
        return CandidateExprs;
    }

    const std::set<clang::Stmt*> & getCandidateMacroExps() {
        return CandidateMacroExps;
    }

    const std::set<clang::Stmt*> & getCandidateIfStmts() {
        return CandidateIfStmts;
    }

    ExprListTy getCandidateEnumConstant(clang::EnumConstantDecl *ECD);

    void dump(bool pretty = true);
};
