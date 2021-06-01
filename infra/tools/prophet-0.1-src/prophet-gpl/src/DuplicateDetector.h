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
#include <string>
#include <vector>
#include <map>

typedef std::map<std::string, std::vector<std::string> > CodeSegTy;

class SourceContextManager;

class DuplicateDetector {
    CodeSegTy resSegs;
    CodeSegTy resPatches;
    std::map<size_t, std::string> lineToPatches;
    bool found;
public:
    // FIXME: This should get const
    DuplicateDetector(SourceContextManager &M, CodeSegTy &codeSegs,
            CodeSegTy &patches);

    CodeSegTy getNewCodeSegments() {
        return resSegs;
    }

    CodeSegTy getNewPatches() {
        return resPatches;
    }

    bool hasDuplicateCodeToPatch() {
        return found;
    }
};
