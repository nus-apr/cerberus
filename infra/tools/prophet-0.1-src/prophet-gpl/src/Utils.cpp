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
#include "sys/time.h"
#include "RepairCandidateGenerator.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdarg.h>
#include <assert.h>
#include <sys/stat.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/AST/ASTContext.h>
#include <fstream>
#include <sstream>
#include <iostream>

using namespace clang;

bool readCodeToString(const std::string &file, std::string &code) {
    FILE* f = fopen(file.c_str(), "r");
    if (f == NULL)
        return false;
    char tmp[1024];
    int ret;
    code = "";
    while ((ret = fread(tmp, 1, 1000, f)) != 0) {
        tmp[ret] = 0;
        code += tmp;
    }
    fclose(f);
    return true;
}

bool readCodeInLines(const std::string &file, std::vector<std::string> &lines) {
    std::string str;
    bool ret = readCodeToString(file, str);
    if (!ret) return false;
    std::string tmp = "";
    lines.clear();
    for (size_t i = 0; i < str.size(); i++) {
        tmp.push_back(str[i]);
        if (str[i] == '\n') {
            lines.push_back(tmp);
            tmp = "";
        }
    }
    if (tmp != "")
        lines.push_back(tmp + "\n");
    return true;
}

std::string stripLine(const std::string &str) {
    size_t idx1 = 0;
    while (idx1 < str.size())
        if (str[idx1] == ' ' || str[idx1] == '\n' || str[idx1] == '\t')
            idx1 ++;
        else
            break;
    size_t idx2 = str.size() - 1;
    while (idx1 <= idx2)
        if (str[idx2] == ' ' || str[idx2] == '\n' || str[idx2] == '\t')
            idx2 --;
        else
            break;
    return str.substr(idx1, idx2 - idx1 + 1);
}

void parseArgFile(const std::string &arg_file, std::string &build_dir, std::vector<std::string> &build_args) {
    FILE *in = fopen(arg_file.c_str(), "r");
    assert(in != NULL);
    char tmps[1000];
    build_args.clear();
    int cnt = fscanf(in, "%s", tmps);
    assert( cnt > 0);
    build_dir = tmps;
    // We need to put extra include directory arguments in to avoid compile error
    // when building AST trees
    std::string extra_paths = EXTRA_CLANG_INCLUDE_PATH;
    std::string tmp = "";
    for (size_t i = 0; i < extra_paths.size(); i++) {
        if (i != extra_paths.size() - 1)
            if ((extra_paths[i] == '-') && (extra_paths[i+1] == 'I')) {
                if (tmp != "") {
                    while (tmp.size() > 1)
                        if (tmp[tmp.size() -1] == ' ')
                            tmp.resize(tmp.size() - 1);
                        else
                            break;
                    build_args.push_back(tmp);
                }
                tmp = "";
            }
        if ((tmp != "") || extra_paths[i] != ' ')
            tmp.push_back(extra_paths[i]);
    }
    if (tmp != "") {
        while (tmp.size() > 1)
            if (tmp[tmp.size() -1] == ' ')
                tmp.resize(tmp.size() - 1);
            else
                break;
        build_args.push_back(tmp);
    }
    while (!feof(in)) {
        cnt = fscanf(in, "%s", tmps);
        if (cnt > 0) build_args.push_back(tmps);
    }
    fclose(in);
}

std::string replace_ext(const std::string &str, const std::string &ext) {
    long idx = str.size() -1;
    while (idx >= 0) {
        if (str[idx] == '.') break;
        idx --;
    }
    if (idx < 0) return str;
    return str.substr(0, idx) + ext;
}

std::string get_ext(const std::string &s) {
    long idx = s.size() -1;
    while (idx >= 0) {
        if (s[idx] == '.') break;
        if (s[idx] == '/') {
            return "";
        }
        idx --;
    }
    if (idx < 0) return "";
    return s.substr(idx+1);
}

bool existFile(const std::string &file) {
    std::ifstream fin(file.c_str(), std::ifstream::in);
    bool ret = fin.is_open();
    if (ret)
        fin.close();
    return ret;
}

bool exist_directory(const std::string &dir) {
    struct stat sb;
    if ((stat(dir.c_str(), &sb) == 0) && S_ISDIR(sb.st_mode))
        return true;
    else
        return false;
}

bool is_header(const std::string &str) {
    std::string ext = get_ext(str);
    // c++ system header have no ext
    return (ext == "h") || (ext == "hpp") || (ext == "") || (ext == "tcc");
//    if (str.size() < 2) return false;
//    return !((str[str.size() - 2] == '.') && (str[str.size() - 1] == 'c'));
}

std::string getFullPath(const std::string &path) {
    char tmp[PATH_MAX];
    char * ret = realpath(path.c_str(), tmp);
    assert( ret != 0);
    return std::string(tmp);
}

int execute_with_timeout(const std::string &cmd, unsigned long timeout) {
    std::ostringstream sout;
    sout << "timeout " << timeout <<  "s " << cmd;
    std::string s = sout.str();
    int ret = system(s.c_str());
    return ret;
}

std::set<std::string> splitStringWithWhite(const std::string &str) {
    std::string tmp = "";
    std::set<std::string> ret;
    ret.clear();
    for (size_t i = 0; i < str.size(); ++i) {
        if (str[i] == ' ')
            if (tmp != "") {
                ret.insert(tmp);
                tmp = "";
            }
        if (str[i] != ' ')
            tmp.push_back(str[i]);
    }
    if (tmp != "")
        ret.insert(tmp);
    return ret;
}

static size_t verbose_level = 1;
static size_t log_level = 10;
static FILE* log_f = NULL;

static struct timeval start_timeval;

void reset_timer() {
    struct timezone tz;
    memset(&tz, 0, sizeof(struct timezone));
    int ret = gettimeofday(&start_timeval, &tz);
    assert( ret == 0);
}

unsigned long long get_timer() {
    struct timezone tz;
    memset(&tz, 0, sizeof(struct timezone));
    struct timeval cur_timeval;
    int ret = gettimeofday(&cur_timeval, &tz);
    assert( ret == 0);
    return cur_timeval.tv_sec - start_timeval.tv_sec;
}

void outlog_open(const char* filename, size_t v_level, size_t l_level) {
    assert(log_f == NULL && "outlog_open() called multiple times!");
    if (l_level != 0) {
        log_f = fopen(filename, "w");
        assert( log_f && "outlog_open() cannot open log file!");
    }
    verbose_level = v_level;
    log_level = l_level;
}

void outlog_close() {
    if (log_f != NULL) fclose(log_f);
    log_f = NULL;
}

int outlog_printf(size_t level, const char* format, ...) {
    va_list args;
    int ret = 0;
    // We are going to print this to the screen
    if (verbose_level >= level) {
        va_start(args, format);
        ret = vfprintf(stdout, format, args);
        fflush(stdout);
        va_end(args);
    }
    // We are going to print this to the logfile
    if (log_level >= level) {
        va_start(args, format);
        ret = vfprintf(log_f, format, args);
        va_end(args);
    }
    return ret;
}

DirectorySwitcher::DirectorySwitcher(const std::string &target_dir) {
    if (getcwd(ori_dir, 1000) == 0)
        assert(0 && "cannot get the current directory!");
    int ret = chdir(target_dir.c_str());
    assert((ret == 0) && "cannot use chdir to change directory!");
}

DirectorySwitcher::~DirectorySwitcher() {
    int ret = chdir(ori_dir);
    assert((ret == 0) && "cannot change back directory!");
}
