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
#include "ASTUtils.h"
#include "BenchProgram.h"
#include <set>
#include <string>

namespace clang {
    class ASTContext;
    class Stmt;
    class Expr;
}

class FeatureParameter;

typedef std::vector<clang::Stmt*> StmtListTy;
typedef std::vector<clang::Expr*> ExprListTy;

class RepairSearchEngine {
    typedef std::set<unsigned long> TestCaseSetTy;
    BenchProgram &P;
    ErrorLocalizer *L;
    TestCaseSetTy negative_cases, positive_cases;
    std::set<std::string> bugged_files;
    bool use_bugged_files;
    bool naive;
    bool learning;
    FeatureParameter *FP;
    // The number of localizaiton result we consider
    unsigned long loc_limit;
    double GeoP;
    // We will just nuke the search space scores and use random search if this is set
    bool random;
    std::string summaryFile;
    unsigned long long timeout_limit;

public:
    RepairSearchEngine(BenchProgram& P, ErrorLocalizer *L, bool naive, bool learning, FeatureParameter *FP)
        : P(P), negative_cases(P.getNegativeCaseSet()), positive_cases(P.getPositiveCaseSet()), naive(naive),
        learning(learning && !naive), FP(FP), GeoP(0.08), random(false), summaryFile(""), timeout_limit(0) {
        this->L = L;
        bugged_files.clear();
        use_bugged_files = false;
        loc_limit = 5000;
    }
    virtual ~RepairSearchEngine() { }
    void setBuggedFile(const std::set<std::string> &bugged_files) {
        use_bugged_files = true;
        this->bugged_files = bugged_files;
    }
    void setLocLimit(unsigned int loc_limit) {
        this->loc_limit = loc_limit;
    }
    void setGeoP(double GeoP) {
        this->GeoP = GeoP;
    }
    void setRandom(bool random) {
        this->random = random;
    }
    void setSummaryFile(const std::string &summaryFile) {
        this->summaryFile = summaryFile;
    }
    int run(const std::string &out_prefix, size_t try_at_least,
            bool print_fix_only, bool full_synthesis);
    void setTimeoutLimit(unsigned long long limit) {
        timeout_limit = limit;
    }
};
