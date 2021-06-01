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
#include <llvm/Support/raw_ostream.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <vector>
#include <string>
#include <stdio.h>

#define dumpNode(k, n) \
    do { \
        if ((k) == StmtKind)\
            (n).stmt->dump();\
        else\
            (n).decl->dump();\
    } \
    while(0)

int main(int argc, char **argv) {
    if (argc > 2) {
        std::vector<std::string> args;
        args.clear();
        for (int i = 3; i < argc; i++)
            args.push_back(argv[i]);
        ASTDiffer differ(argv[1], argv[2], args);
        if (!differ.Diff())
            return 1;
        else {
            std::vector<DiffResultEntry> res;
            unsigned int distance = differ.GetDiffResult(res);
            llvm::errs() << "Distance " << distance << "\n";
            for (size_t i = 0; i < res.size(); i++) {
                llvm::errs() << "=========================\n";
                if (res[i].DiffActionKind == DiffResultEntry::InsertAction) {
                    llvm::errs() << "Insert:\n";
                    dumpNode(res[i].NodeKind2, res[i].Node2);
                    llvm::errs() << "At:\n";
                    dumpNode(res[i].NodeKind1, res[i].Node1);
                }
                else if (res[i].DiffActionKind == DiffResultEntry::DeleteAction) {
                    llvm::errs() << "Delete:\n";
                    dumpNode(res[i].NodeKind1, res[i].Node1);
                }
                else {
                    llvm::errs() << "Replace:\n";
                    dumpNode(res[i].NodeKind1, res[i].Node1);
                    llvm::errs() << "With\n";
                    dumpNode(res[i].NodeKind2, res[i].Node2);
                }
            }
        }
    }
}
