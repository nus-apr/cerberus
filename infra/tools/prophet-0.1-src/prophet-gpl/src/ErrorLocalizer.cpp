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
#include "ErrorLocalizer.h"
#include "BenchProgram.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/Expr.h>

using namespace clang;

NaiveErrorLocalizer::NaiveErrorLocalizer(BenchProgram &P): P(P) {
    std::string src_dir = P.getSrcdir();
    // We cheat to get filename and line number
    std::ifstream fin((src_dir + "/__cheat.log").c_str(), std::ifstream::in);
    assert( fin.is_open() && "Cannot find the cheat file!");
    std::string filename;
    size_t line_number, column_number;
    candidateLocations.clear();
    while (fin >> filename) {
        fin >> line_number;
        fin >> column_number;
        candidateLocations.push_back(SourcePositionTy(filename, line_number));
    }
    fin.close();
}

std::ostream & operator << (std::ostream &os, const SourcePositionTy &a) {
    os << a.toString();
    return os;
}

llvm::raw_ostream & operator << (llvm::raw_ostream &os, const SourcePositionTy &a) {
    os << a.toString();
    return os;
}

std::istream & operator >> (std::istream &os, SourcePositionTy &a) {
    os >> a.expFilename >> a.expLine >> a.expColumn >> a.spellFilename >> a.spellLine >> a.spellColumn;
    return os;
}
