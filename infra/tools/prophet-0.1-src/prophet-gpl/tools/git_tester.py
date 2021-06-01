# Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
# Prophet
# 
# This file is part of Prophet.
# 
# Prophet is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# Prophet is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
import subprocess
from os import path, chdir, getcwd, walk, system
import shutil
from tester_common import get_fix_revisions

def switch_to(out_dir, revision):
    ori_dir = getcwd();
    chdir(out_dir);
    ret = subprocess.call(["git", "checkout", revision, "-f"]);
    if ret != 0:
        print "Failed to swtich to the revision " + revision;
        chdir(ori_dir);
        return False;

    ret = subprocess.call(["autoreconf", "-fvi"]);
    if ret != 0:
        print "Failed to create config, check autoconf!";
        chdir(ori_dir);
        return False;
    ret = subprocess.call(["./configure"]);
    if ret != 0:
        print "Failed to run configure!";
        chdir(ori_dir);
        return False;
    subprocess.call(["make", "clean"]);
    ret = subprocess.call(["make", "-j", "2"]);
    if ret != 0:
        print "Failed to compile!";
        chdir(ori_dir);
        return False;
    chdir(ori_dir);
    return True;

def _gettestcase_id(s):
    id = s.rfind(".");
    if s[id+1:] != "sh":
        return -1;
    if s[0] != 't':
        return -1;
    for i in range(1, 5):
        if s[i] > '9' or s[i] < '0':
            return -1;
    return int(s[1:5])

def extract_test_cases(out_dir = "git-src-tests", repo_dir = ""):
    if path.exists(out_dir):
        s = raw_input(out_dir + " exists! continue and override (y/n)?")
        if s[0] != "y":
            return True;
        else:
            shutil.rmtree(out_dir);
    addr = "https://github.com/git/git.git";

    if repo_dir != "":
        tmp_repo = repo_dir;
        cleanup = False;
    else:
        tmp_repo = "__git-src";
        ret = system("git clone " + addr + " " + out_dir + "/git-src");
        if ret != 0:
            print "git-clone failed, check your network and git!";
            shutil.rmtree(tmp_repo);
            return False;
        cleanup = True;

    shutil.copytree(tmp_repo + "/t", out_dir);
    d = {};
    for root, dirs, files in walk(tmp_repo + "/t"):
        for file in files:
            idx = _gettestcase_id(file);
            if idx != -1:
                d[idx] = file;
    f = open(out_dir + "/testfile.log", "w")
    print >>f, len(d);
    for key in sorted(d.keys()):
        print >> f, d[key];
    f.close();

    if cleanup:
        shutil.rmtree(tmp_repo);
    return True

class git_initializer:
    def display_info(self, repo_dir):
        ori_dir = getcwd();
        chdir(repo_dir);
        ret = subprocess.call(["git", "remote", "-v"]);
        chdir(ori_dir);
        return ret == 0;
    def reset(self, repo_dir):
        ori_dir = getcwd();
        chdir(repo_dir);
        ret = subprocess.call(["git", "checkout", "master", "-f"]);
        chdir(ori_dir);
        return ret == 0;
    def create_repo(self, repo_dir, log_file):
        github_addr = "https://github.com/git/git.git"
        if path.exists(repo_dir):
            shutil.rmtree(repo_dir);
        ret = system("git clone "+github_addr+" "+repo_dir);
        if ret != 0:
            print "Failed to grab from github, check your network connection and make sure you have git!";
            return False;
        f = open(log_file, "w");
        ret = get_fix_revisions(repo_dir);
        for fix_r, previous_r, comment in ret:
            print >>f, "Fix Revision: " + fix_r;
            print >>f, "Previous Revision: " + previous_r;
            print >>f, "Comment:";
            print >>f, comment;
        f.close();
        return True;

    def extract_tests(self, repo_dir, test_dir):
        return extract_test_cases(test_dir, repo_dir);

class git_tester:
    def __init__(self, work_dir, repo_dir, test_dir):
        self.repo_dir = repo_dir;
        self.test_dir = test_dir;
        self.work_dir = work_dir;
        f = open(test_dir + "/testfile.log", "r");
        lines = f.readlines();
        self.testfiles = [];
        for i in range(1, len(lines)):
            self.testfiles.append(lines[i].strip(" ").strip("\n"));
        self.n = int(lines[0].strip());
        assert(self.n == len(self.testfiles));

    def getn(self):
        return self.n;

    def set_revision(self, revision):
        print self.repo_dir + " " + revision;
        ret = switch_to(self.repo_dir, revision);
        if ret:
            print "Done reset revision to " + revision;
        else:
            print "Failed to build revision " + revision;
        return ret;

    def _test(self, i):
        ori_dir = getcwd();
        chdir(self.tmptest_dir);
        test_cmd = "./" + self.testfiles[i];
        p = subprocess.Popen([test_cmd], stdout = subprocess.PIPE);
        (out, err) = p.communicate();
        chdir(ori_dir);
        lines = out.strip().split("\n");
        check_line = lines[len(lines) - 2];
        tokens = check_line.split();
        if len(tokens) < 2:
            return False;
        return tokens[1] == "passed";

    def test_all(self):
        self.tmptest_dir = self.repo_dir + "/__tests";
        if (path.exists(self.tmptest_dir)):
            shutil.rmtree(self.tmptest_dir);
        print "preparing clean test dir...";
        shutil.copytree(self.test_dir, self.tmptest_dir);
        ret = set();
        for i in range(0, self.n):
            print "Testing " + str(i),
            if self._test(i):
                print " ok"
                ret.add(i);
            else:
                print " failed"
        return ret;
