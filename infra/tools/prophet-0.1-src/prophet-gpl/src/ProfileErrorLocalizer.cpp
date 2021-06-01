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
#include "config.h"
#include "Utils.h"
#include "ProfileErrorLocalizer.h"
#include "BenchProgram.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include <map>
#include <queue>
#include <fstream>
#include <assert.h>

#include <dirent.h>

using namespace clang;

#define CLANG_PROFILE_WRAP "pclang.py"

#define SIGMA 1000000
#define LOC_LIMIT 4980
#define LOC2_LIMIT 20

extern llvm::cl::opt<bool> ForCPP;

void ProfileErrorLocalizer::clearProfileResult() {
    std::string cmd = "rm -rf /tmp/__run*.log";
    int res = system(cmd.c_str());
    assert(res == 0);
}

std::map<SourcePositionTy, ProfileInfoTy> ProfileErrorLocalizer::parseProfileResult() {
    if (LI == NULL)
        LI = new LocationIndex(INDEX_FILE);

    std::map<SourcePositionTy, ProfileInfoTy> M;
    M.clear();
    DIR* dp = opendir("/tmp");
    struct dirent *dirp;
    while (((dirp = readdir(dp)))) {
        std::string nstr = dirp->d_name;
        if ((nstr.substr(0,5) != "__run") || (nstr.substr(nstr.size() - 4, 4) != ".log"))
            continue;

        std::ifstream fin(("/tmp/" + nstr).c_str(), std::ifstream::in);
        std::string line1, line2;
        std::string pid = nstr.substr(5, nstr.size() - 4 - 5);
        // We get an empty pid, FIXME investigate why this will happen
        if (pid == "") {
            fprintf(stderr, "Cannot get pid value, assume 0.");
            llvm::errs() << nstr << "\n";
            assert(0);
            pid = "0";
        }

        while (std::getline(fin, line1)) {
            if (line1 == "") break;
            std::getline(fin, line2);
            SourcePositionTy tmploc;
            {
                std::istringstream sin(line1);
                unsigned long idx;
                sin >> idx;
                tmploc = LI->getProfileLocation(idx);
                //llvm::errs() << "Previous filepath: " << tmploc.expFilename  << "\n";
                tmploc.expFilename = P.normalizePath(tmploc.expFilename);
                //llvm::errs() << "Trimed filepath: " << tmploc.expFilename << "\n";
                tmploc.spellFilename = P.normalizePath(tmploc.spellFilename);
            }
            long long cnt, cnt2;
            {
                std::istringstream sin(line2);
                sin >> cnt >> cnt2;
            }
            std::map<SourcePositionTy, ProfileInfoTy>::iterator
                find_it = M.find(tmploc);
            if (find_it == M.end()) {
                ProfileInfoTy tmp;
                tmp.execution_cnt = cnt;
                tmp.beforeend_cnt = cnt2;
                tmp.pid = pid;
                M.insert(std::make_pair(tmploc, tmp));
            }
            else {
                find_it->second.execution_cnt += cnt;
                if (find_it->second.beforeend_cnt < cnt2) {
                    find_it->second.beforeend_cnt = cnt2;
                    find_it->second.pid = pid;
                }
            }
        }
        fin.close();
    }
    closedir(dp);

    return M;
}

void clearTmpDirectory() {
    int ret = system("rm -rf /tmp/__* /tmp/pclang*");
    assert(ret == 0);
}

ProfileErrorLocalizer::ProfileErrorLocalizer(BenchProgram &P,
        const std::set<std::string> &bugged_files, bool skip_build):
    P(P), negative_cases(P.getNegativeCaseSet()), positive_cases(P.getPositiveCaseSet()) {
    LI = NULL;
    if (skip_build) {
        P.addExistingSrcClone("profile", true);
    }
    else {
        P.clearSrcClone("profile");
        P.createSrcClone("profile");
        BenchProgram::EnvMapTy envMap;
        envMap.clear();
        if (ForCPP.getValue())
            envMap["COMPILE_CMD"] = "clang++";
        else
            envMap["COMPILE_CMD"] = CLANG_CMD;
        envMap["INDEX_FILE"] = INDEX_FILE;
        clearTmpDirectory();
        P.buildSubDir("profile", CLANG_PROFILE_WRAP, envMap);
    }

    typedef std::map<SourcePositionTy, ProfileInfoTy> ProfileLocationMapTy;
    ProfileLocationMapTy negative_mark;
    negative_mark.clear();
/*    ProfileLocationMapTy negative_cnt;
    negative_cnt.clear();*/
    std::map<SourcePositionTy, long long> positive_mark;
    //ProfileLocationMapTy positive_mark;
    positive_mark.clear();
/*    ProfileLocationMapTy positive_cnt;
    positive_cnt.clear();*/

    // We test with an unmodified environment
    BenchProgram::EnvMapTy testEnv;
    testEnv.clear();

    unsigned long min_id = 1000000;
    unsigned long max_id = 0;
    for (TestCaseSetTy::const_iterator it = negative_cases.begin(); it != negative_cases.end(); ++it) {
        llvm::errs() << "Neg Processing: "<< *it << "\n";
        ProfileLocationMapTy res;
        clearProfileResult();
        bool tmp = P.test("profile", *it, testEnv, true);
        res = parseProfileResult();

        if (*it < min_id) min_id = *it;
        if (*it > max_id) max_id = *it;
        assert( !tmp || 1);
        for (ProfileLocationMapTy::iterator iit = res.begin(); iit != res.end(); ++iit) {
            //llvm::errs() << iit->first.expFilename << " "<< iit->first.expLine << "\n";
            if (negative_mark.count(iit->first) != 0) {
                negative_mark[iit->first].execution_cnt ++;
                if (negative_mark[iit->first].beforeend_cnt < iit->second.beforeend_cnt) {
                    negative_mark[iit->first].beforeend_cnt = iit->second.beforeend_cnt;
                    negative_mark[iit->first].pid = iit->second.pid;
                }
            }
            else {
                negative_mark[iit->first].execution_cnt = 1;
                negative_mark[iit->first].beforeend_cnt = iit->second.beforeend_cnt;
                negative_mark[iit->first].pid = iit->second.pid;
            }
        }
    }

    if (min_id < 200) min_id = 0; else min_id -= 200;
    max_id += 200;

    TestCaseSetTy::const_iterator begin_pos = positive_cases.lower_bound(min_id);
    TestCaseSetTy::const_iterator end_pos = positive_cases.upper_bound(max_id);

    size_t cnt = 0;
    for (TestCaseSetTy::const_iterator it = begin_pos; it != end_pos; ++it) {
        llvm::errs() << "Processing: " << cnt << " : " << *it << "\n";
        ProfileLocationMapTy res;
        clearProfileResult();
        bool tmp = P.test("profile", *it, testEnv, true);
        res = parseProfileResult();
        cnt ++;
        if (!tmp) {
            fprintf(stderr, "Profile version failed on this, maybe because of timeout due to overhead!\n");
            continue;
        }
        for (ProfileLocationMapTy::iterator iit = res.begin(); iit != res.end(); ++iit) {
            positive_mark[iit->first]++;//+= iit->second.first;
        }
    }

    typedef std::priority_queue<std::pair<std::pair<long long, long long>, std::pair<SourcePositionTy, std::string> > >
        PriorQueueTy;
    PriorQueueTy Q, Q2;
    for (ProfileLocationMapTy::iterator it = negative_mark.begin(); it != negative_mark.end(); ++it) {
        //llvm::errs() << it->first.expFilename << " " << it->first.expLine <<"\n";
        if (isSystemHeader(it->first.expFilename)) {
            continue;
        }
        Q.push(std::make_pair( std::make_pair(-(it->second.execution_cnt * SIGMA - positive_mark[it->first]),
            (it->second.beforeend_cnt)), std::make_pair(it->first, it->second.pid) ));
        while (Q.size() > LOC_LIMIT)
            Q.pop();

        // FIXME: this is really hacky
        if (bugged_files.size() != 0)
            if (bugged_files.count(it->first.expFilename) == 1) {
                Q2.push(std::make_pair( std::make_pair(-(it->second.execution_cnt * SIGMA - positive_mark[it->first]),
                    (it->second.beforeend_cnt)), std::make_pair(it->first, it->second.pid) ));
                while (Q2.size() > LOC2_LIMIT)
                    Q2.pop();
            }
    }
    //assert(0);

    std::vector<ResRecordTy> tmpv, tmpv2;
    tmpv.clear();
    candidateResults.clear();
    while (Q.size() > 0) {
        ResRecordTy tmp;
        tmp.primeScore = - Q.top().first.first;
        tmp.secondScore = Q.top().first.second;
        tmp.loc = Q.top().second.first;
        tmp.pid = Q.top().second.second;
        //llvm::errs() << tmp.loc << "\t\t" << tmp.primeScore << "\t\t" << tmp.secondScore << "\t\t@" << Q.top().second.second << "\n";
        /*llvm::errs() << tmp.loc.expFilename << ":" << tmp.loc.expLine << ","
            << tmp.loc.expColumn << "\t\t" << tmp.primeScore << "\n";*/
        tmpv.push_back(tmp);
        Q.pop();
    }
    tmpv2.clear();
    // FIXME: this is really hacky
    while (Q2.size() > 0) {
        ResRecordTy tmp;
        tmp.primeScore = - Q2.top().first.first;
        tmp.secondScore = Q2.top().first.second;
        tmp.loc = Q2.top().second.first;
        tmp.pid = Q2.top().second.second;
        bool found = false;
        for (size_t i = 0; i < tmpv.size(); i++)
            if (!(tmpv[i].loc < tmp.loc) && !(tmp.loc < tmpv[i].loc)) {
                found = true;
                break;
            }
        if (!found) tmpv2.push_back(tmp);
        Q2.pop();
    }

    for (long i = (long)tmpv.size() - 1; i >=0; --i)
        candidateResults.push_back(tmpv[i]);
    for (long i = (long)tmpv2.size() - 1; i >= 0; --i)
        candidateResults.push_back(tmpv2[i]);

    printResult(P.getLocalizationResultFilename());
}

std::vector<SourcePositionTy> ProfileErrorLocalizer::getCandidateLocations() {
    std::vector<SourcePositionTy> ret;
    ret.clear();
    for (size_t i = 0; i < candidateResults.size(); i++)
        ret.push_back(candidateResults[i].loc);
    return ret;
}

void ProfileErrorLocalizer::printResult(const std::string &outfile) {
    std::ofstream fout(outfile.c_str(), std::ofstream::out);
    assert( fout.is_open() );
    for (size_t i = 0; i < candidateResults.size(); ++i) {
        ResRecordTy tmp = candidateResults[i];
        fout << tmp.loc << "\t\t" << tmp.primeScore << "\t\t" << tmp.secondScore << "\t\t" << tmp.pid << "\n";
    }
    fout.close();
}

ProfileErrorLocalizer::ProfileErrorLocalizer(BenchProgram &P, const std::string &res_file)
    : P(P), negative_cases(P.getNegativeCaseSet()), positive_cases(P.getPositiveCaseSet())
{
    LI = NULL;
    std::ifstream fin(res_file.c_str(), std::ifstream::in);
    assert(fin.is_open());
    ResRecordTy tmp;
    candidateResults.clear();
    std::string line = "";
    size_t cnt = 0;
    while (std::getline(fin, line)) {
        cnt ++;
        if (line == "")
            continue;
        std::istringstream sin(line);
        sin >> tmp.loc;
        sin >> tmp.primeScore >> tmp.secondScore >> tmp.pid;
        if (tmp.pid == "") {
            fprintf(stderr, "Corrupted file at line %lu, assume pid 0\n", (unsigned long)cnt);
            tmp.pid = "0";
        }
        candidateResults.push_back(tmp);
    }
    fin.close();
}
