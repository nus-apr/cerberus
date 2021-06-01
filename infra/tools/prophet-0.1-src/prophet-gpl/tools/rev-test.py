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
from sys import argv
from os import system
from php_tester import php_tester

if __name__ == "__main__":
    assert(len(argv) > 3);
    repo_src = argv[1];
    repo_test = argv[2];
    revision = argv[3];
    if (len(argv) == 4):
        out_file = "revlog" + revision + ".txt";
        revision2 = revision + "^1";
        deps_dir = "php-deps";
    else:
        assert(len(argv) > 6);
        revision2 = argv[4];
        out_file = argv[5];
        deps_dir = argv[6];

    workdir = "__tmp" + revision;
    system("mkdir " + workdir);
    repo1 = workdir + "/tmp1";
    repo2 = workdir + "/tmp2";
    testdir = workdir + "/tests";
    system("cp -rf "+ repo_src + " " + repo1);
    system("cp -rf "+ repo_src + " " + repo2);
    system("cp -rf "+ repo_test + " " + testdir);

    tester1 = php_tester(workdir, repo1, testdir);
    tester2 = php_tester(workdir, repo2, testdir);

    ret = tester1.set_revision(revision, deps_dir);
    assert(ret);
    ret = tester2.set_revision(revision2, deps_dir);
    assert(ret);
    s1 = tester1.test_all();
    s2 = tester2.test_all();

    s1.discard(7648);
    s1.discard(6551);
    s1.discard(6702);
    s1.discard(10982);
    s2.discard(7648);
    s2.discard(6551);
    s2.discard(6702);
    s2.discard(10982);

    diff12 = s1 - s2;
    diff21 = s2 - s1;
    common = s1 & s2;
    fout = open(out_file, "w");
    print >>fout, "-";
    print >>fout, "-";
    outdiff = [];
    for i in diff12:
        # repeat 5 times for non-determinism
        bad = False;
        for j in range(0, 5):
            tmp = set();
            tmp.add(i);
            r1 = tester1.test(tmp);
            r2 = tester2.test(tmp);
            if (len(r1) != 1):
                bad = True;
                break;
            if (len(r2) != 0):
                bad = True;
                break;
        if not bad:
            outdiff.append(i);
    print >>fout, "Diff Cases: Tot", len(outdiff);
    for i in outdiff:
        print >>fout, i,
    print >>fout;
    print >>fout, "Positive Cases: Tot", len(common);
    for i in common:
        print >>fout, i,
    print >>fout;
    print >>fout, "Regression Cases: Tot", len(diff21);
    for i in diff21:
        print >>fout, i,
    print >>fout;
    fout.close();

    system("rm -rf " + workdir);
