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
#include "Utils.h"
#include "ErrorLocalizer.h"
#include <string>
#include <vector>
#include <set>
#include <map>

#define INDEX_FILE "/tmp/__index.loc"

class BenchProgram;

struct ProfileInfoTy {
    long long execution_cnt;
    long long beforeend_cnt;
    std::string pid;
};

class ProfileErrorLocalizer : public ErrorLocalizer {
    typedef std::set<unsigned long> TestCaseSetTy;

    BenchProgram &P;

    TestCaseSetTy negative_cases, positive_cases;

    class ResRecordTy {
    public:
        long long primeScore;
        long long secondScore;
        SourcePositionTy loc;
        std::string pid;
    };

    std::vector<ResRecordTy> candidateResults;

    LocationIndex *LI;

    void clearProfileResult();

    std::map<SourcePositionTy, ProfileInfoTy> parseProfileResult();

public:
    ProfileErrorLocalizer(BenchProgram &P, const std::string &res_file);

    ProfileErrorLocalizer(BenchProgram &P, const std::set<std::string> &bugged_file,
            bool skip_build);

    virtual std::vector<SourcePositionTy> getCandidateLocations();

    virtual void printResult(const std::string &outfile);

    virtual ~ProfileErrorLocalizer() { }
};
