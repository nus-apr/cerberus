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
#include "BenchProgram.h"
#include "Utils.h"
#include "clang/Tooling/Tooling.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>
#include <sstream>
#include <fstream>
#include <llvm/Support/raw_ostream.h>

#include <dirent.h>
#include <libexplain/system.h>

#define LOCALIZATION_RESULT "profile_localization.res"
#define CONFIG_FILE_PATH "repair.conf"
#define SOURCECODE_BACKUP "__backup"
#define SOURCECODE_BACKUP_LOG "__backup.log"
#define LDBACKUP "ld-backup"

static std::string getRndName() {
    std::string ret = "__tmp";
    for (size_t i = 0; i < 5; i++)
        ret += 'a' + (rand() % 26);
    return ret;
}

static void execute_cmd_until_succ(const std::string &cmd) {
    int ret = 0;
    do {
        ret = explain_system_on_error(cmd.c_str());
        if (ret != 0) {
            fprintf(stderr, "Invoke %s failed, will try again after 1 sec.!\n", cmd.c_str());
            sleep(1);
        }
    }
    while (ret != 0);
}

BenchProgram::BenchProgram(const std::string &configFileName, const std::string &workDirPath,
        bool no_clean_up): config(configFileName) {
    Init(workDirPath, no_clean_up);
}

BenchProgram::BenchProgram(const std::string &workDirPath)
    : config(workDirPath + "/" + CONFIG_FILE_PATH) {
    Init(workDirPath, true);
}

ConfigFile* BenchProgram::getCurrentConfig() {
    return &config;
}

void BenchProgram::createSrcClone(const std::string &subDir) {
    assert( src_dirs.count(subDir) == 0);
    std::string cmd = "cp -rf ";
    cmd += ori_src_dir + " " + work_dir + "/" + subDir;
    execute_cmd_until_succ(cmd);
    src_dirs.insert(std::make_pair(subDir, false));
}

void BenchProgram::clearSrcClone(const std::string &subDir) {
    std::string cmd = "rm -rf ";
    cmd += work_dir + "/" + subDir;
    execute_cmd_until_succ(cmd);
    src_dirs.erase(subDir);
}

void BenchProgram::addExistingSrcClone(const std::string &subDir, bool built) {
    src_dirs[subDir] = built;
}

static void parseRevisionLog(const std::string& revision_file,
        BenchProgram::TestCaseSetTy &negative_cases,
        BenchProgram::TestCaseSetTy &positive_cases) {
    std::ifstream fin(revision_file.c_str(), std::ifstream::in);
    std::string line;
    std::getline(fin,line);
    std::getline(fin,line);
    std::getline(fin,line);
    unsigned long n1, n2;
    char tmp_array[100];
    sscanf(line.c_str(), "%s %s %s %lu", tmp_array, tmp_array, tmp_array, &n1);
    std::getline(fin,line);
    std::istringstream sin(line.c_str());
    negative_cases.clear();
    for (size_t i = 0; i < n1; i++) {
        size_t id;
        sin >> id;
        negative_cases.insert(id);
    }
    std::getline(fin,line);
    sscanf(line.c_str(), "Positive Cases: Tot %lu", &n2);
    std::getline(fin,line);
    std::istringstream sin2(line.c_str());
    positive_cases.clear();
    for (size_t i = 0; i < n2; i++) {
        size_t id;
        sin2 >> id;
        positive_cases.insert(id);
    }
    fin.close();
    assert((negative_cases.size() != 0) && "No negative cases, bad revision log!");
}

/*BenchProgram::BenchProgram(const std::string &src_dir, const std::string &test_dir,
                           const std::string &build_cmd, const std::string &test_cmd,
                           const std::string &run_work_dir, bool using_ramfs,
                           bool no_clean_up, size_t case_timeout)*/
void BenchProgram::Init(const std::string &workDirPath, bool no_clean_up)
{
    compile_cnt = 0;
    test_cnt = 0;
    this->cache = NULL;
    this->no_clean_up = no_clean_up;
    this->ori_src_dir = config.getStr("src_dir");
    this->wrap_ld = false;
    if (config.hasValue("wrap_ld"))
        this->wrap_ld = (config.getStr("wrap_ld") == "yes");
    if ((workDirPath == "") || (!exist_directory(workDirPath))) {
        int ret;
        std::string cmd;
        if (workDirPath == "") {
            do {
                this->work_dir = getRndName();
                std::string cmd = "mkdir ";
                ret = system((cmd + work_dir).c_str());
            }
            while (ret != 0);
        }
        else {
            this->work_dir = workDirPath;
            std::string cmd = "mkdir ";
            ret = system((cmd + work_dir).c_str());
            assert( ret == 0 );
        }
        this->work_dir = getFullPath(this->work_dir);
        // This part is obsolete, it seems it will not add much performance
        /*if (using_ramfs) {
            cmd = "mount -t ramfs ramfs ";
            cmd += work_dir;
            ret = system(cmd.c_str());
            if (ret != 0) {
                fprintf(stderr, "You should run it with root permission!\n");
                exit(1);
            }
            cmd = "chmod a+w ";
            ret = system((cmd + work_dir).c_str());
            assert(ret == 0);
        }*/

        // We create an initial clone of the basic src direcotry
        src_dirs.clear();
        createSrcClone("src");
        this->src_dir = getFullPath(this->work_dir + "/src");

        std::string ori_test_dir = config.getStr("test_dir");
        if (ori_test_dir != "") {
            cmd = "cp -rf ";
            cmd += ori_test_dir + " " + work_dir + "/tests";
            ret = system(cmd.c_str());
            assert(ret == 0);
        }
    }
    else {
        this->work_dir = getFullPath(workDirPath);
        this->src_dir = getFullPath(work_dir + "/src");
        src_dirs.clear();
        src_dirs.insert(std::make_pair("src", true));

        // If we just in middle of repair, we need to restore before we go on
        std::ifstream fin((work_dir + "/" + SOURCECODE_BACKUP_LOG).c_str(), std::ifstream::in);
        if (fin.is_open()) {
            std::string target_file;
            char tmp[1000];
            size_t cnt = 0;
            int ret;
            std::string cmd;
            while (fin.getline(tmp, 1000)) {
                target_file = tmp;
                {
                    std::ostringstream sout;
                    sout << "cp -rf "  << work_dir << "/" << SOURCECODE_BACKUP << cnt << " " << src_dir << "/" << target_file;
                    cmd = sout.str();
                }
                ret = system(cmd.c_str());
                assert( ret == 0);
                {
                    std::ostringstream sout;
                    sout << "rm -rf " << work_dir << "/" << SOURCECODE_BACKUP << cnt;
                    cmd = sout.str();
                }
                ret = system(cmd.c_str());
                assert( ret == 0);
            }
            fin.close();
            cmd = "rm -rf " + work_dir + "/" + SOURCECODE_BACKUP_LOG;
            ret = system(cmd.c_str());
            assert( ret == 0);
        }
    }

    dep_dir = config.getStr("dep_dir");
    if (dep_dir != "")
        dep_dir = getFullPath(dep_dir);

    this->test_dir = getFullPath(work_dir+"/tests");
    this->build_log_file = work_dir + "/build.log";
    // Clean up builg log for every execution
    std::string cmd = std::string("rm -rf ") + build_log_file;
    int ret = system(cmd.c_str());
    assert( ret == 0);
    this->build_cmd = getFullPath(config.getStr("build_cmd"));
    this->test_cmd = getFullPath(config.getStr("test_cmd"));
    this->localization_filename = work_dir + "/" + LOCALIZATION_RESULT;

    // The files for controling timeout stuff
    total_repair_build_time = 0;
    repair_build_cnt = 0;
    this->case_timeout = 60;
    if (config.getStr("single_case_timeout") != "") {
        std::istringstream sin(config.getStr("single_case_timeout"));
        sin >> case_timeout;
    }

    std::string revision_file = config.getStr("revision_file");
    parseRevisionLog(revision_file, negative_cases, positive_cases);
}

BenchProgram::~BenchProgram() {
    int ret;
    std::string cmd;
    outlog_printf(0, "Total number of compiles: %lu\n", compile_cnt);
    outlog_printf(0, "Total number of test eval: %lu\n", test_cnt);
    // This is obsolete
    /*if (using_ramfs) {
        cmd = "umount ";
        cmd += work_dir;
        ret = system(cmd.c_str());
        if (ret != 0)
            fprintf(stderr, "unmount failed!\n");
    }*/
    if (!no_clean_up) {
        cmd = "rm -rf ";
        cmd += work_dir;
        ret = system(cmd.c_str());
        if (ret != 0)
            fprintf(stderr, "remove work dir failed\n");
    }
    if (cache != NULL)
        delete cache;
}

void BenchProgram::getCompileMisc(const std::string &src_file, std::string &build_dir,
                                  std::vector<std::string> &build_args) {
    if (!src_dirs["src"]) {
        buildFull("src");
        src_dirs["src"] = true;
    }
    std::string cmd;
    if (dep_dir != "")
        cmd = build_cmd + " -p " + dep_dir + " -c -d " + src_file + " " + src_dir + " __args >>" + build_log_file + " 2>&1";
    else
        cmd = build_cmd + " -c -d " + src_file + " " + src_dir + " __args >>" + build_log_file + " 2>&1";
    int sys_ret = explain_system_on_error(cmd.c_str());
    assert( sys_ret == 0 );
    parseArgFile("__args", build_dir, build_args);
    sys_ret = explain_system_on_error("rm -rf __args");
    if (sys_ret != 0)
        fprintf(stderr, "Remove __args failed!\n");
    src_dirs["src"] = true;
/*    fprintf(stderr, "Arguments we get:\n");
    for (size_t i = 0; i < build_args.size(); ++i)
        fprintf(stderr, "\"%s\"\n", build_args[i].c_str());*/
}

bool incrementalBuild(time_t timeout_limit, const std::string &src_dir, const std::string &build_log) {
    char ori_dir[1000];
    char* retc = getcwd(ori_dir, 1000);
    assert(retc != NULL);
    int ret = chdir(src_dir.c_str());
    assert(ret == 0);
    //FIXME: ugly for php
    ret = system("rm -rf ext/phar/phar.php");
    assert(ret == 0);
    if (timeout_limit == 0)
        ret = execute_with_timeout((std::string("make >>") + build_log + " 2>&1"), 60);
    else
        ret = execute_with_timeout((std::string("make >>") + build_log + " 2>&1"), timeout_limit);

    bool succ = (ret == 0);
    ret = chdir(ori_dir);
    assert(ret == 0);
    return succ;
}

bool BenchProgram::buildFull(const std::string &subDir, time_t timeout_limit, bool force_reconf) {
    assert(src_dirs.count(subDir) != 0);
    std::string src_dir = getFullPath(work_dir + "/" + subDir);
    if (force_reconf || !src_dirs[subDir]) {
        std::string cmd;
        if (dep_dir != "")
            cmd = build_cmd + " -p " + dep_dir + " "+ src_dir + " >>" + build_log_file + " 2>&1";
        else
            cmd = build_cmd + " " + src_dir + " >>" + build_log_file + " 2>&1";
        int ret;
        if (timeout_limit == 0)
            ret = system(cmd.c_str());
        else
            ret = execute_with_timeout(cmd.c_str(), timeout_limit);
        src_dirs[subDir] = true;
        return ret == 0;
    }
    else {
        return incrementalBuild(timeout_limit, src_dir, build_log_file);
    }
}

/*void BenchProgram::configOnly() {
    std::string cmd = build_cmd + " -x " + src_dir + " >>" + build_log_file + " 2>&1";
    int ret = system(cmd.c_str());
    assert(ret == 0);
}*/

void BenchProgram::pushWrapPath(const std::string &wrap_path, const std::string &cc_path) {
    // We are going to set wrap path before everything, so that it will replace offcial
    // gcc/cc compiler
    ori_path_for_wrap_path = getenv("PATH");
    std::string new_path = CLANG_WRAP_PATH;
    new_path += ":" + ori_path_for_wrap_path;
    int ret = setenv("PATH", new_path.c_str(), 1);
    assert( ret == 0 );

    // Copy it to the wrap path
    std::string cmd = "cp -rf " + wrap_path + "/" + cc_path + " " + wrap_path + "/cc";
    ret = system(cmd.c_str());
    assert( ret == 0);
    cmd = "cp -rf " + wrap_path + "/" + cc_path + " " + wrap_path + "/gcc";
    ret = system(cmd.c_str());
    assert( ret == 0);
    // This is to copy g++
    cmd = "cp -rf " + wrap_path + "/" + cc_path + " " + wrap_path + "/g++";
    ret = system(cmd.c_str());
    assert( ret == 0);
    cmd = "rm -rf " + wrap_path + "/ld";
    ret = system(cmd.c_str());
    assert( ret == 0);
    if (wrap_ld) {
        cmd = "cp -rf " + wrap_path + "/" + std::string(LDBACKUP) + " " + wrap_path + "/ld";
        ret = system(cmd.c_str());
        assert( ret == 0);
    }
    /*cmd = "cp -rf " + wrap_path + "/" + cc_path + " " + wrap_path + "/ld";
    ret = system(cmd.c_str());
    assert( ret == 0);*/
}

void BenchProgram::popWrapPath() {
    int ret = setenv("PATH", ori_path_for_wrap_path.c_str(), 1);
    assert( ret == 0);
}

void BenchProgram::pushEnvMap(const EnvMapTy &envMap) {
    ori_env_map.clear();
    for (EnvMapTy::const_iterator it = envMap.begin();
            it != envMap.end(); ++it) {
        char *old_v = getenv(it->first.c_str());
        if (old_v != NULL)
            ori_env_map[it->first] = old_v;
        int res = setenv(it->first.c_str(), it->second.c_str(), 1);
        assert( res == 0);
    }
}

void BenchProgram::popEnvMap(const EnvMapTy &envMap) {
    for (EnvMapTy::const_iterator it = envMap.begin();
            it != envMap.end(); ++it) {
        int res;
        if (ori_env_map.count(it->first) == 0)
            res = unsetenv(it->first.c_str());
        else
            res = setenv(it->first.c_str(), ori_env_map[it->first].c_str(), 1);
        assert( res == 0);
    }
    ori_env_map.clear();
}

bool BenchProgram::buildSubDir(const std::string &subDir, const std::string &wrapScript,
        const EnvMapTy &envMap) {
    pushEnvMap(envMap);

    pushWrapPath(CLANG_WRAP_PATH, wrapScript);
    time_t timeout_limit = 0;
    if (repair_build_cnt > 10)
        timeout_limit = ((total_repair_build_time / repair_build_cnt) + 1) * 2 + 10;

    bool succ = false;
    {
        //llvm::errs() << "Build repaired code with timeout limit " << timeout_limit << "\n";
        ExecutionTimer timer;
        succ = buildFull(subDir, timeout_limit);
        if (succ) {
            total_repair_build_time += timer.getSeconds();
            repair_build_cnt ++;
        }
    }
    popWrapPath();

    popEnvMap(envMap);
    return succ;
}

bool BenchProgram::buildWithRepairedCode(const std::string &wrapScript, const EnvMapTy &envMap,
        const std::map<std::string, std::string> &fileCodeMap) {
    compile_cnt ++;
    // This is to backup the changed sourcefile, in case something broken
    // the workdir, and we want to just resume
    std::ofstream fout2((work_dir + "/" + SOURCECODE_BACKUP_LOG).c_str(), std::ofstream::out);
    size_t cnt = 0;
    for (std::map<std::string, std::string>::const_iterator it = fileCodeMap.begin();
            it != fileCodeMap.end(); ++it) {
        std::string target_file = it->first;
        if (target_file[0] != '/')
            target_file = src_dir + "/" + target_file;
        // Copy the backup
        std::ostringstream sout;
        sout << "cp -f " << target_file << " " << work_dir << "/" << SOURCECODE_BACKUP << cnt;
        std::string cmd = sout.str();
        execute_cmd_until_succ(cmd);
        cnt ++;
        fout2 << normalizePath(target_file) << "\n";
        fout2.flush();
        std::ofstream fout(target_file.c_str(), std::ofstream::out);
        fout << it->second;
        fout.close();
        // remove the .o and .lo files to recompile
        {
            std::string tmp = replace_ext(target_file, ".o");
            std::string cmd = "rm -f "  + tmp;
            execute_cmd_until_succ(cmd);
        }
        {
            std::string tmp = replace_ext(target_file, ".lo");
            std::string cmd = "rm -f "  + tmp;
            execute_cmd_until_succ(cmd);
        }
    }
    fout2.close();

    bool succ = buildSubDir("src", wrapScript, envMap);

    // Remove temporary backup file, because we have done it
    cnt = 0;
    for (std::map<std::string, std::string>::const_iterator it = fileCodeMap.begin();
            it != fileCodeMap.end(); ++ it) {
        std::string target_file = it->first;
        if (target_file[0] != '/')
            target_file = src_dir + "/" + it->first;
        else
            target_file = it->first;
        std::ostringstream sout;
        sout << "mv -f " << work_dir << "/" << SOURCECODE_BACKUP << cnt << " " << target_file;
        std::string cmd = sout.str();
        execute_cmd_until_succ(cmd);
        cnt ++;
        // Make sure it refresh the build system to avoid cause problem
        cmd = std::string("touch ") + target_file;
        execute_cmd_until_succ(cmd);
        // remove the .o and .lo files to force recompile next time
        {
            std::string tmp = replace_ext(target_file, ".o");
            std::string cmd = "rm -f "  + tmp;
            execute_cmd_until_succ(cmd);
        }
        {
            std::string tmp = replace_ext(target_file, ".lo");
            std::string cmd = "rm -f "  + tmp;
            execute_cmd_until_succ(cmd);
        }
    }

    std::string cmd = "rm -rf " + work_dir + "/__backup.log";
    execute_cmd_until_succ(cmd);
    return succ;
}

/*void BenchProgram::prepare_test() {
    std::string cmd = test_cmd + " " + src_dir + " " + test_dir + " " + work_dir;
    int ret = system(cmd.c_str());
    assert(ret == 0);
}*/

BenchProgram::TestCaseSetTy BenchProgram::testSet(const std::string &subDir,
        const TestCaseSetTy &case_set, const EnvMapTy &env_pairs, bool pass_basic_src_dir) {
    if (case_set.size() == 0)
        return std::set<unsigned long>();

    // Prepare test script to generate test result
    std::string cmd;
    if (!pass_basic_src_dir)
        cmd = test_cmd + " " + getFullPath(work_dir + "/" + subDir) + " " + test_dir + " " + work_dir + " ";
    else
        cmd = test_cmd + " -p " + getFullPath(work_dir + "/" + subDir) + " " + src_dir + " " + test_dir + " " + work_dir + " ";
    std::ostringstream sout;
    sout << cmd;
    for (TestCaseSetTy::const_iterator it = case_set.begin(); it != case_set.end(); it ++)
        sout << *it << " ";
    sout <<  " > __res\n";
    cmd = sout.str();

    int res;

    pushEnvMap(env_pairs);
    /*for (std::map<std::string, std::string>::const_iterator it = env_pairs.begin();
            it != env_pairs.end(); ++it) {
        res = setenv(it->first.c_str(), it->second.c_str(), 1);
        assert( res == 0);
    }*/

    // case_timeout controls the timeout of each executed test case
    if (case_set.size() != 1)
        res = system(cmd.c_str());
    else {
        res = execute_with_timeout(cmd.c_str(), case_timeout);
    }

    std::set<unsigned long> ret;
    ret.clear();
    // return value is zero, or just count as a total failure
    if (res == 0) {
        FILE *in = fopen("__res", "r");
        assert(in != NULL);
        unsigned long id;
        while (!feof(in)) {
            res = fscanf(in, "%ld", &id);
            if (res > 0) ret.insert(id);
            if (res == 0) break;
        }
        fclose(in);
    }
    else {
        //FIXME:What the hell is this ?
        res = system("rm -rf __clean*");
        if (res != 0)
            fprintf(stderr, "strange I/O problem!\n");
    }
    res = system("rm -rf __res");
    if (res != 0)
        fprintf(stderr, "rm __res failed\n");

    popEnvMap(env_pairs);
    /*for (std::map<std::string, std::string>::const_iterator it = env_pairs.begin();
            it != env_pairs.end(); ++it) {
        res = setenv(it->first.c_str(), "", 1);
        assert( res == 0);
    }*/
    return ret;
}

bool BenchProgram::test(const std::string &subDir, size_t id, const EnvMapTy &envMap,
        bool pass_basic_src_dir) {
    test_cnt ++;
    TestCaseSetTy tmp;
    tmp.clear();
    tmp.insert(id);
    TestCaseSetTy res = testSet(subDir, tmp, envMap, pass_basic_src_dir);
    return res.size() == 1;
}

bool BenchProgram::verifyTestCases() {
    buildFull("src");
    //prepare_test();
    std::set<unsigned long> tmp = testSet("src", negative_cases, std::map<std::string, std::string>());
    if (tmp.size() != 0) {
        outlog_printf(0, "Unexpected pass:\n");
        for (std::set<unsigned long>::iterator it = tmp.begin(); it != tmp.end(); ++it)
            outlog_printf(0, "%lu\n", *it);
        return false;
    }
    tmp = testSet("src", positive_cases, std::map<std::string, std::string>());
    if (tmp.size() != positive_cases.size()) {
        outlog_printf(0, "Unexpected fail:\n");
        for (std::set<unsigned long>::iterator it = positive_cases.begin(); it != positive_cases.end(); ++it)
            if (tmp.count(*it) == 0)
                outlog_printf(0, "%lu\n", *it);
        outlog_printf(0, "Only passed tot: %lu\n", tmp.size());
        return false;
        //fprintf(stderr, "Eliminate not passed cases!\n");
        //positive_cases = tmp;
        //return true;
    }
    outlog_printf(0, "All passed!\n");
    return true;
}

static std::string trimPath(const std::string &str, const std::string &sub_str) {
    std::string ret = str;
    size_t idx = ret.find(sub_str);
    if (idx != std::string::npos) {
        idx += sub_str.size();
        size_t cnt = 0;
        while ((cnt != 2) && (idx < str.size())) {
            if (str[idx] == '/')
                cnt ++;
            idx ++;
        }
        ret = ret.substr(idx);
    }
    if (ret.size() >= 2) {
        if ((ret[0] == '.') && (ret[1] == '/'))
            ret = ret.substr(2);
    }
    return ret;
}

std::string BenchProgram::normalizePath(const std::string &str) {
    return trimPath(str, work_dir);
}

/*void BenchProgram::skipProfileBuild() {
    profile_dir = work_dir + "/profile";
}*/

/*bool BenchProgram::testProfile(size_t id,
        std::map<SourcePositionTy, ProfileInfoTy> &M) {
    assert(profile_dir != "");
    std::string cmd = "rm -rf /tmp/__run*.log";
    int res = system(cmd.c_str());
    assert(res == 0);

    cmd = test_cmd + " -p " + profile_dir + " " + src_dir + \
                      " " + test_dir + " " + work_dir + " ";
    std::ostringstream sout;
    sout << cmd;
    sout << id;
    sout <<  " > __res\n";
    cmd = sout.str();
    res = system(cmd.c_str());
    assert( res == 0);
    FILE *in = fopen("__res", "r");
    assert( in != NULL );
    bool ret = false;
    while (!feof(in)) {
        size_t tmp;
        res = fscanf(in, "%ld", &tmp);
        if (tmp == id)
            ret = true;
        if (res == 0) break;
    }
    fclose(in);
    res = system("rm -rf __res");
    if (res != 0)
        fprintf(stderr, "rm __res failed\n");

    if (LI == NULL)
        LI = new LocationIndex(INDEX_FILE);

    M.clear();
    DIR* dp = opendir("/tmp");
    struct dirent *dirp;
    while (((dirp = readdir(dp)))) {
        std::string nstr = dirp->d_name;
        if ((nstr.substr(0,5) != "__run") || (nstr.substr(nstr.size() - 4, 4) != ".log"))
            continue;

        std::ifstream fin(("/tmp/" + nstr).c_str(), std::ifstream::in);
        std::string line1, line2;
        while (std::getline(fin, line1)) {
            if (line1 == "") break;
            std::getline(fin, line2);
            SourcePositionTy tmploc;
            {
                std::istringstream sin(line1);
                size_t idx;
                sin >> idx;
                tmploc = LI->getProfileLocation(idx);
                //llvm::errs() << "Previous filepath: " << tmploc.expFilename  << "\n";
                tmploc.expFilename = trimPath(tmploc.expFilename, work_dir);
                //llvm::errs() << "Trimed filepath: " << tmploc.expFilename << "\n";
                tmploc.spellFilename = trimPath(tmploc.spellFilename, work_dir);
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
                tmp.pid = nstr.substr(5, nstr.size() - 4 - 5);
                M.insert(std::make_pair(tmploc, tmp));
            }
            else {
                find_it->second.execution_cnt += cnt;
                if (find_it->second.beforeend_cnt < cnt2) {
                    find_it->second.beforeend_cnt = cnt2;
                    find_it->second.pid = nstr.substr(5, nstr.size() - 4 - 5);
                }
            }
        }
        fin.close();
    }
    closedir(dp);

    return ret;
}*/

/*void BenchProgram::setArgFile(const std::string &fixtest_argfile) {
    parseArgFile(fixtest_argfile, infile_build_dir, infile_args);
    use_arg_file = true;
}*/

std::unique_ptr<clang::ASTUnit> BenchProgram::buildClangASTUnit(const std::string &file, const std::string &code) {
    std::string build_dir;
    std::vector<std::string> args;
    this->getCompileMisc(file, build_dir, args);
    char ori_dir[1000];
    if (getcwd(ori_dir, 1000) == 0)
        assert(0 && "Failed to get current directory path!\n");
    std::string target = build_dir;
    if (target == ".")
        target = src_dir;

    // Include an implicit header lookup path of the current directory
    std::vector<std::string> tmpArgs;
    tmpArgs.clear();
    std::string full_key_path = getFullPath(src_dir + "/" + file);
    size_t idx = full_key_path.rfind("/");
    assert( idx != std::string::npos);
    tmpArgs.push_back("-I");
    tmpArgs.push_back(full_key_path.substr(0, idx));
    tmpArgs.insert(tmpArgs.end(), args.begin(), args.end());

    int ret = chdir(target.c_str());
    assert( ret == 0 );
    fprintf(stderr, "going to directory %s\n", target.c_str());
    std::unique_ptr<clang::ASTUnit> unit = clang::tooling::buildASTFromCodeWithArgs(code, tmpArgs, file);
    ret = chdir(ori_dir);
    assert( ret == 0 );
    return unit;
}

/*void BenchProgram::clearProfileBuild() {
    std::string cmd = "rm -rf " + work_dir + "/profile";
    int ret = system(cmd.c_str());
    assert( ret == 0);
}*/
