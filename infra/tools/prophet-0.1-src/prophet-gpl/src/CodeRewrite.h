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
#include "ExprSynthesizer.h"
#include <string>

class SourceContextManager;

typedef std::map<size_t, clang::Expr*> ExprFillInfo;
typedef std::map<std::string, std::vector<std::string> > CodeSegTy;
typedef std::map<std::string, std::string> NewCodeMapTy;

NewCodeMapTy mergeCode(const CodeSegTy &codeSegs, const std::vector<CodeSegTy> &patches);

bool canMerge(const CodeSegTy &codeSegs, const CodeSegTy &patches);

NewCodeMapTy combineCode(const CodeSegTy &codeSegs, const CodeSegTy &patch);

class CodeRewriter {
    CodeSegTy resCodeSegs, resPatches;
public:
    CodeRewriter(SourceContextManager &M, const RepairCandidate &rc, ExprFillInfo *pefi);

    CodeSegTy getCodeSegments() {
        return resCodeSegs;
    }

    CodeSegTy getPatches() {
        return resPatches;
    }

    NewCodeMapTy getCodes() {
        return combineCode(resCodeSegs, resPatches);
    }
};

