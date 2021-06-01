#!/usr/bin/env python
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
from php_tester import php_tester, php_initializer
from git_tester import git_tester, git_initializer
from sys import argv
from os import path, mkdir, remove
import time
import shutil
import subprocess

if __name__ == "__main__":
    if len(argv) < 3:
        print "Usage: revision-tester.py <php|git> <out_dir> [<# of parallel> <id of parallel>]"
        exit(1);
    app = argv[1];
    out_dir = argv[2];
    if len(argv) < 4:
        para_n = 1;
        para_id = 0;
    else:
        para_n = int(argv[3]);
        para_id = int(argv[4]);

    workdir = "__tmp" + str(para_id);
    if path.exists(workdir):
        shutil.rmtree(workdir);
    mkdir(workdir);
    ret = subprocess.call(["mount", "-t", "ramfs", "ramfs", workdir]);
    if ret != 0:
        print "Need root to start this program!";
        exit(1);
    ret = subprocess.call(["chmod", "a+w", workdir]);
    if ret != 0:
        print "Need root to change permision!";
        exit(1);

    master_repo = "__tmpmaster";
    if para_id == 0:
        if app == "php":
            init = php_initializer();
        else:
            init = git_initializer();
        if path.exists(out_dir+"/done.0"):
            remove(out_dir + "/done.0");
        if path.exists(out_dir):
            s = raw_input(out_dir+" exists, overwrite?(y/n)");
            if s[0] != 'y':
                exit(0);
            shutil.rmtree(out_dir);
        # if there is repo, skip the git clone process
        ok = False;
        if path.exists(master_repo):
            ret = init.display_info(master_repo);
            if ret:
                s = raw_input("ok to proceed?(y/n)");
                if s[0] == 'y':
                    ret = init.reset(master_repo);
                    if ret:
                        ok = True;
                    else:
                        print "Bad repository in " + master_repo + "refetch!";

        if not ok:
            ret = init.create_repo(master_repo, "__fixes.log");
            if not ret:
                print "Failed to fetch! abort!";
                exit(1);

        ret = init.extract_tests(master_repo, out_dir);
        if not ret:
            print "Failed to extract test cases";
            exit(1);
        open(out_dir+"/done.0", "w").close();
    else:
        # wait for the master to finish
        while not path.exists(out_dir+"/done.0"):
            time.sleep(1);

    tmprepo1 = workdir + "/tmp1";
    tmprepo2 = workdir + "/tmp2";
    shutil.copytree(master_repo, tmprepo1);
    shutil.copytree(master_repo, tmprepo2);
    testdir = workdir + "/tests";
    shutil.copytree(out_dir, testdir);

    if app == "php":
        tester1 = php_tester(workdir, tmprepo1, testdir);
        tester2 = php_tester(workdir, tmprepo2, testdir);
    else:
        tester1 = git_tester(workdir, tmprepo1, testdir);
        tester2 = git_tester(workdir, tmprepo2, testdir);

    cnt = 0;
    f = open("__fixes.log", "r");
    lines = f.readlines();
    f.close();
    fix_revision = "";
    for line in lines:
        tokens = line.strip("\n").strip(" ").split();
        if (len(tokens) < 2):
            continue;
        if (tokens[0] == "Fix") and (tokens[1] == "Revision:"):
            fix_revision = tokens[2];
        if (tokens[0] == "Previous") and (tokens[1] == "Revision:"):
            if cnt % para_n == para_id:
                fout = open(out_dir + "/revision-" + fix_revision + "-" + tokens[2] + ".log", "w")
                ret = tester1.set_revision(fix_revision);
                if not ret:
                    print >> fout, "Failed to build revision" + fix_revision;
                    fout.close();
                    cnt = cnt + 1;
                    continue;
                ret = tester2.set_revision(tokens[2]);
                if not ret:
                    print >> fout, "Failed to build revision" + tokens[2];
                    fout.close();
                    cnt = cnt + 1;
                    continue;
                s1 = tester1.test_all();
                s2 = tester2.test_all();
                diff = s1 - s2;
                if (len(s2 - s1) == 0):
                    if len(diff) != 0:
                        print >> fout, "Fix Revision: " + fix_revision;
                        print >> fout, "Previous Revision: " + tokens[2];
                        print >> fout, "Diff Cases: Tot " + str(len(diff));
                        for id in diff:
                            print >> fout, id,
                        print >>fout;
                        print >>fout, "Positive Cases: Tot " + str(len(s2));
                        for id in s2:
                            print >> fout, id,
                        print >>fout;
                        fout.close();
                    else:
                        print >>fout, "No diff";
                        print >>fout, "Positive Cases: Tot " + str(len(s2));
                        for id in s2:
                            print >> fout, id,
                        print >>fout;
                        fout.close();
                else:
                    print >>fout, "Bad fixes, regression!";
                    print >>fout, "Regression Cases: Tot " + str(len(s2 - s1));
                    for id in s2 - s1:
                        print >>fout, id,
                    print >>fout;
                    fout.close();
                print "===================Done No." + str(cnt) + " Case================";
            cnt = cnt + 1;

    subprocess.call(["umount", workdir]);
    shutil.rmtree(workdir);
