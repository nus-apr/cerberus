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
#include "ErrorLocalizer.h"
#include "ProfileErrorLocalizer.h"
#include "ConfigFile.h"
#include <clang/Frontend/ASTUnit.h>
#include <string>
#include <vector>
#include <set>
#include <map>

class ConfigFile;

class LocationIndex;

class TestCache {
    std::string cache_file;
    std::map<std::string, bool> cache;

    void appendFile(const std::string &key, size_t v) {
        FILE *f = fopen(cache_file.c_str(), "ab");
        assert(f);
        size_t n = key.size();
        size_t ret = fwrite(&n, sizeof(n), 1, f);
        assert(ret == 1);
        ret = fwrite(&key[0], 1, key.size(), f);
        assert( ret == key.size());
        ret = fwrite(&v, sizeof(v), 1, f);
        assert( ret == 1);
        fclose(f);
    }

public:
    TestCache(const std::string &cache_file): cache_file(cache_file), cache() {
        if (!existFile(cache_file)) {
            FILE* f = fopen(cache_file.c_str(), "wb");
            fclose(f);
        }
        else {
            FILE* f = fopen(cache_file.c_str(), "rb");
            while (!feof(f)) {
                size_t n;
                size_t ret = fread(&n, sizeof(n), 1, f);
                if (ret != 1) {
                    assert(feof(f));
                    break;
                }
                std::string key;
                key.resize(n);
                ret = fread(&key[0], 1, n, f);
                assert( ret == n);
                ret = fread(&n, sizeof(n), 1, f);
                if (n == 0 && (cache.count(key) == 0))
                    cache.insert(std::make_pair(key, false));
                if (n == 1)
                    cache.insert(std::make_pair(key, true));
            }
            fclose(f);
        }
    }

    void addCandidate(const std::string &key) {
        if (cache.count(key) == 0) {
            appendFile(key, 0);
            cache[key] = false;
        }
    }

    bool isNotSucc(const std::string &key) {
        if (cache.count(key) != 0)
            return !cache[key];
        else
            return false;
    }

    void markSucc(const std::string &key) {
        if (cache.count(key) == 0 || cache[key] == false) {
            cache[key] = true;
            appendFile(key, 1);
        }
    }
};


class BenchProgram {
public:
    typedef std::set<unsigned long> TestCaseSetTy;
    typedef std::map<std::string, std::string> EnvMapTy;
private:
    ConfigFile config;
    // The name of the work directory, all paths in this class are absolute paths
    std::string work_dir;
    // The path name of the original src_directory from the config file
    // This must be present in the file system ortherwise, we will hit errors!
    std::string ori_src_dir;
    // The basic src directory path
    std::string src_dir;
    // The set of created src_directories, including the basic source directory,
    // all of them are cped from the ori_src_dir. The map indicates whether this
    // gets built or not
    std::map<std::string, bool> src_dirs;
    // The test directory path inside work_dir, this is an absolute path!
    std::string test_dir;
    // The dependency directory path, this is an absolute path!
    std::string dep_dir;
    // The build command script path, this is an absolute path!
    std::string build_cmd;
    // The test command script path, this is an absolute path!
    std::string test_cmd;

    std::string profile_dir;

    std::string localization_filename;
    std::string build_log_file;
    bool no_clean_up;
    bool wrap_ld;

    std::string infile_build_dir;
    std::vector<std::string> infile_args;

    time_t total_repair_build_time;
    size_t repair_build_cnt;
    size_t case_timeout;

    TestCaseSetTy positive_cases, negative_cases;

    unsigned long compile_cnt;
    unsigned long test_cnt;

    TestCache *cache;

    void Init(const std::string &workDirPath, bool no_clean_up);

    bool buildFull(const std::string &subDir, time_t timeout_limit = 0, bool force_reconf = false);

    void getCompileMisc(const std::string &src_file, std::string &build_dir, std::vector<std::string> &build_args);

    EnvMapTy ori_env_map;

    void pushEnvMap(const EnvMapTy &envMap);

    void popEnvMap(const EnvMapTy &envMap);

    std::string ori_path_for_wrap_path;

    void pushWrapPath(const std::string &wrapPath, const std::string &cc_path);

    void popWrapPath();

public:

    // We create the work dir from a configuration file, and we will put workdir
    // in the workDirPath path. If it is empty string, we will create a work dir
    // with an empty directory
    BenchProgram(const std::string &configFileName, const std::string &workDirPath,
            bool no_clean_up = false);

    BenchProgram(const std::string &workDirPath);

    TestCaseSetTy getPositiveCaseSet() {
        return positive_cases;
    }

    TestCaseSetTy getNegativeCaseSet() {
        return negative_cases;
    }

    ConfigFile* getCurrentConfig();

    void createSrcClone(const std::string &subDir);

    void clearSrcClone(const std::string &subDir);

    void addExistingSrcClone(const std::string &subDir, bool built);

    std::unique_ptr<clang::ASTUnit> buildClangASTUnit(const std::string &src_file,
            const std::string &code);

    bool buildSubDir(const std::string &subDir, const std::string &wrapScript,
            const EnvMapTy &envMap);

    bool buildWithRepairedCode(const std::string &wrapScript, const EnvMapTy &envMap,
            const std::map<std::string, std::string> &fileCodeMap);

    TestCaseSetTy testSet(const std::string &subDir, const TestCaseSetTy &case_set,
            const EnvMapTy &envMap, bool pass_basic_src_dir = false);

    bool test(const std::string &subDir, size_t id, const EnvMapTy &envMap,
            bool pass_basic_src_dir);

/*    BenchProgram(const std::string &src_dir, const std::string &test_dir,
            const std::string &build_cmd, const std::string &test_cmd,
            const std::string &run_work_dir, bool using_ramfs = false,
            bool no_clean_up = false, size_t case_timeout = 60);*/

    std::string getLocalizationResultFilename() {
        return localization_filename;
    }

    std::string getWorkdir() { return work_dir; }

    std::string getSrcdir() { return src_dir; }

    std::string normalizePath(const std::string &);

    //void setArgFile(const std::string &fixtest_argfile);

    //void clearProfileBuild();

    //void skipProfileBuild();

    //void buildProfile();

    //void configOnly();

    //void prepare_test();

    //std::set<size_t> test(const std::set<size_t> &case_set,
    //        const std::map<std::string, std::string> &env_pairs);

    //bool testProfile(size_t id, std::map<SourcePositionTy, ProfileInfoTy> &M);

    bool verifyTestCases();

    virtual ~BenchProgram();

    // Create a testcache object, this can only be called once
    TestCache *getTestCache() {
        if (cache == NULL)
            cache = new TestCache(work_dir + "/test.cache");
        return cache;
    }
};
