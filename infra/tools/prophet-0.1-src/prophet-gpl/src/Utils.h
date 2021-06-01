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
#include <algorithm>
#include <vector>
#include <string>
#include <set>
#include <time.h>

// This is the set of wrappers for output
void outlog_open(const char* filename, size_t v_level, size_t l_level);
int outlog_printf(size_t level, const char* format, ...);
void outlog_close();

namespace clang {
    class ASTContext;
    class CompoundStmt;
    class Stmt;
}

bool readCodeToString(const std::string &file, std::string &code);

bool readCodeInLines(const std::string &file, std::vector<std::string> &lines);

void parseArgFile(const std::string &arg_file, std::string &build_dir, std::vector<std::string> &build_args);

std::string stripLine(const std::string &);

std::string get_ext(const std::string &s);

std::string replace_ext(const std::string &str, const std::string &ext);

bool existFile(const std::string &file);

bool exist_directory(const std::string &dir);

bool is_header(const std::string &str);

std::string getFullPath(const std::string &path);

std::set<std::string> splitStringWithWhite(const std::string &str);

int execute_with_timeout(const std::string &cmd, unsigned long timeout);

void reset_timer();

unsigned long long get_timer();

static inline bool isSystemHeader(const std::string &str) {
    if (str.size() < 4) return false;
    return str.substr(0,4) == "/usr";
}

class ExecutionTimer {
    struct timespec start_time;
public:
    ExecutionTimer() {
        clock_gettime(CLOCK_MONOTONIC, &start_time);
    }

    time_t getSeconds() {
        struct timespec now_time;
        clock_gettime(CLOCK_MONOTONIC, &now_time);
        return now_time.tv_sec - start_time.tv_sec;
    }
};

class DirectorySwitcher {
    char ori_dir[1000];
public:
    DirectorySwitcher(const std::string &target_dir);

    ~DirectorySwitcher();
};
