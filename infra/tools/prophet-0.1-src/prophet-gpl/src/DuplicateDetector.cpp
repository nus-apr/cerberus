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
#include "DuplicateDetector.h"
#include "SourceContextManager.h"
#include <llvm/Support/raw_ostream.h>
#include <map>
#include <vector>
#include <assert.h>
#include <cstring>

typedef std::map<size_t, size_t> StringMatchResTy;

static inline StringMatchResTy matchTwo(const std::string &s1, const std::string &s2) {
    long **f;
    long **d;
    f = new long*[s1.size() + 10];
    d = new long*[s1.size() + 10];
    for (size_t i = 0; i < s1.size() + 10; i++) {
        f[i] = new long[s2.size() + 10];
        d[i] = new long[s2.size() + 10];
        memset(f[i], 0, (s2.size() + 10) * sizeof(long));
        memset(d[i], 0, (s2.size() + 10) * sizeof(long));
    }

    for (size_t i = 1; i <= s1.size(); i++)
        for (size_t j = 1; j <= s2.size(); j++) {
            f[i][j] = f[i-1][j];
            if (s1[i-1] == ' ')
                f[i][j]++;
            d[i][j] = 0;
            if (f[i][j-1] > f[i][j]) {
                f[i][j] = f[i][j-1];
                d[i][j] = 1;
            }
            if (s1[i-1] == s2[j-1])
                if (f[i-1][j-1] + 1 > f[i][j]) {
                    f[i][j] = f[i-1][j-1] + 1;
                    d[i][j] = 2;
                }
        }

    StringMatchResTy res;
    res.clear();
    size_t i = s1.size();
    size_t j = s2.size();
    while ((i != 0) && (j != 0)) {
        if (d[i][j] == 2) {
            res.insert(std::make_pair(i - 1, j - 1));
            i --; j --;
        }
        else if (d[i][j] == 1)
            j --;
        else
            i --;
    }

    for (size_t i = 0; i < s1.size() + 10; i++) {
        delete f[i];
        delete d[i];
    }
    delete f;
    delete d;

    return res;
}

static inline int getCharType(char c) {
    if (c == ' ' || c == '\n' || c == '\t')
        return 1;
    if (c >='A' && c <='Z')
        return 0;
    if (c >='a' && c <='z')
        return 0;
    if (c >='0' && c <='9')
        return 0;
    if (c == '_')
        return 0;
    return 2;
}

static inline std::string stripAllWhite(const std::string &s1) {
    std::string ret = "";
    int last_type = 1;
    bool omitted = false;
    for (size_t i = 0; i < s1.size(); i++) {
        int new_type = getCharType(s1[i]);
        if (new_type != 1) {
            if (omitted && (new_type == last_type) && (last_type != 1) && (ret[ret.size() - 1] != '(') && (ret[ret.size() -1] != ')')
                    && (s1[i] != '(') && (s1[i] != ')')) {
                ret.push_back(' ');
            }
            ret.push_back(s1[i]);
            omitted = false;
        }
        else
            omitted = true;
        if (new_type != 1)
            last_type = new_type;
    }
    return ret;
}

static inline std::string replaceStr(const std::string &master, const std::string &sub,
        size_t idx, size_t len, const std::string &new_sub) {
    std::string ret = master;
    size_t id;
    size_t start = 0;
    while ((id = ret.find(sub, start)) != std::string::npos) {
        ret = ret.substr(0, id + idx) + new_sub + ret.substr(id + idx + len);
        start = id + idx + len;
    }
    return ret;
}

static inline size_t extend_to_token(const std::string &str, size_t idx, int direction) {
    long long ret = idx;
    while ( ret >= 0 && ret < (long long)str.size()) {
        long long next = ret + direction;
        if (next < 0 || next >= (long long)str.size())
            return ret;
        if (getCharType(str[ret]) != getCharType(str[next]))
            return ret;
        ret = next;
    }
    assert(0);
    return ret;
}

static size_t scanNLine(const std::string &code, size_t my_start, size_t n) {
    size_t my_end = my_start;
    size_t cnt = 0;
    while (my_end < code.size()) {
        if (code[my_end] == '\n')
            cnt ++;
        my_end ++;
        if (cnt == n) break;
    }
    return my_end;
}

#define MIN_STR_LENGTH 200
#define BETA 20

DuplicateDetector::DuplicateDetector(SourceContextManager &M, CodeSegTy &codeSegs,
        CodeSegTy &patches) {
    resSegs.clear();
    resPatches.clear();
    found = false;
    for (CodeSegTy::iterator it = codeSegs.begin(); it != codeSegs.end(); ++ it) {
        std::string src_file = it->first;
        // XXX: We only work for trivial patches
        if (patches[src_file].size() > 1) {
            found = false;
            resSegs.clear();
            resPatches.clear();
            return;
        }
        // XXX: This is nasty wiring code
        std::string code = M.getSourceCode(src_file);
        std::string patch = patches[src_file][0];
        // FIXME: We avoid too large chunk, avoid creating
        // everything for macro.
        if (patch.size() > 200) {
            found = false;
            resSegs.clear();
            resPatches.clear();
            return;
        }
        size_t start_idx = codeSegs[src_file][0].size();
        size_t end_idx = code.size() - codeSegs[src_file][1].size();

        // 1st step is to stretch the [start_idx, end_idx) into
        // two lines, we use this substr to locate duplicate code
        size_t my_start = start_idx;
        while (my_start > 0) {
            if (code[my_start - 1] != '\n')
                my_start --;
            else
                break;
        }
        size_t step = 2;
        size_t my_end = scanNLine(code, my_start, step);
        while (my_end < code.size() && ((my_end - my_start < MIN_STR_LENGTH))) {
            my_end = scanNLine(code, my_end, 1);
            step++;
        }
        if (end_idx > my_end) {
            resSegs.clear();
            resPatches.clear();
            return;
        }
        std::string sub_s = code.substr(my_start, my_end - my_start);
        std::string old_s = code.substr(start_idx, end_idx - start_idx);

        // 2nd step is for every two lines, find cloned part of this sub
        size_t cur_idx = 0;
        size_t line_cnt = 1;
        std::vector<std::pair<std::pair<size_t, size_t>, std::string> > replaceList;
        replaceList.clear();
        replaceList.push_back(std::make_pair(std::make_pair(start_idx, end_idx), patch));
        lineToPatches.clear();

        while (cur_idx < code.size()) {
            if (abs(cur_idx-my_start) > MIN_STR_LENGTH * 2) {
                size_t cur_end = scanNLine(code, cur_idx, step);
                std::string sub_s2 = code.substr(cur_idx, cur_end - cur_idx);
                std::string s1 = stripAllWhite(sub_s);
                std::string s2 = sub_s2;
                size_t size1 = s1.size();
                size_t size2 = stripAllWhite(s2).size();
                if (abs((long long)size1 - size2) * BETA <= (long long)size1 + (long long)size2) {
                    StringMatchResTy res = matchTwo(s1, sub_s2);
                    size_t delta = size1 + size2 - 2 * res.size();
                    if (delta * BETA <= size1 + size2) {
                        // This is a cloned place
                        // 3rd step is to replace the patch string in a way that
                        // will fit this
                        std::string sub_s1 = stripAllWhite(old_s);
                        size_t base_idx = s1.find(sub_s1);
                        assert(base_idx != std::string::npos);
                        std::string new_patch = stripAllWhite(patch);

                        // Sometimes the top and last cannot find the match, we
                        // are just going to extend to the token
                        size_t s_idx = 0;
                        size_t e_idx = 0;
                        if (res.count(base_idx + 0) != 0)
                            s_idx = res[0];
                        else {
                            size_t i = 0;
                            while (i < sub_s1.size() && (res.count(base_idx + i) == 0)) i ++;
                            assert(res.count(base_idx + i) != 0);
                            s_idx = extend_to_token(s2, res[base_idx + i], -1);
                        }

                        if (res.count(base_idx + sub_s1.size() -1 ) != 0)
                            e_idx = res[base_idx + sub_s1.size() - 1];
                        else {
                            long long i = sub_s1.size() - 1;
                            while (i >= 0 && (res.count(base_idx + i) == 0))
                                i --;
                            //assert(res.count(base_idx + i) != 0);
                            // FIXME FIXME: really hacky!!!!
                            if (res.count(base_idx +i ) == 0) {
                                resSegs.clear();
                                resPatches.clear();
                                return;
                            }
                            e_idx = extend_to_token(s2, res[base_idx + i], 1);
                        }

                        // Replace each small token
                        size_t i = 0;
                        while (i < sub_s1.size()) {
                            if (res.count(base_idx + i) == 0) {
                                size_t j = i;
                                while (j < sub_s1.size() && (res.count(base_idx + j) == 0))
                                    j++;
                                size_t core_end = 0;
                                size_t len = j - i;
                                if (j == sub_s1.size()) {
                                    core_end = e_idx + 1;
                                }
                                else {
                                    assert(res.count(base_idx + j) == 1);
                                    core_end = res[base_idx + j];
                                }
                                while (j < sub_s1.size() && (res.count(base_idx + j) == 1))
                                    j++;
                                long long k = i - 1;
                                size_t core_start = 0;
                                if (k == -1)
                                    core_start = s_idx;
                                else {
                                    assert(res.count(base_idx + k) == 1);
                                    core_start = res[base_idx + k] + 1;
                                }
                                while (k >= 0 && (res.count(base_idx + k) == 1))
                                    k --;
                                k = k + 1;
                                std::string x1 = sub_s1.substr(k, j - k);

                                std::string x2 = s2.substr(core_start, core_end - core_start);
                                new_patch = replaceStr(new_patch, x1, i - k, len, x2);
                                i = j;
                            }
                            else
                                i ++;
                        }

                        size_t new_start = cur_idx + s_idx;
                        size_t new_end = cur_idx + e_idx + 1;
                        replaceList.push_back(std::make_pair(std::make_pair(new_start, new_end),
                                new_patch));
                        lineToPatches.insert(std::make_pair(line_cnt, new_patch));

                        cur_idx = cur_end;
                        line_cnt += step;
                        //llvm::errs() << "Done3\n";
                    }
                    else {
                        cur_idx = scanNLine(code, cur_idx, 1);
                        line_cnt ++;
                    }
                }
                else {
                    cur_idx = scanNLine(code, cur_idx, 1);
                    line_cnt ++;
                }
            }
            else {
                line_cnt ++;
                cur_idx = scanNLine(code, cur_idx, 1);
            }
        }

        resSegs[src_file].clear();
        resPatches[src_file].clear();
        if (replaceList.size() > 0) {
            std::sort(replaceList.begin(), replaceList.end());
            cur_idx = 0;
            for (size_t i = 0; i < replaceList.size(); i++) {
                resSegs[src_file].push_back(code.substr(cur_idx,
                            replaceList[i].first.first - cur_idx));
                resPatches[src_file].push_back(replaceList[i].second);
                cur_idx = replaceList[i].first.second;
            }
            resSegs[src_file].push_back(code.substr(cur_idx, code.size() - cur_idx));
            if (replaceList.size() > 1)
                found = true;
        }
        else {
            // XXX: this might be problematic
            found = false;
            resSegs.clear();
            resPatches.clear();
            return;
        }
    }
}
