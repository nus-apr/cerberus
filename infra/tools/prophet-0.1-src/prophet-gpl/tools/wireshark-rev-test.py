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
from os import system, getcwd, chdir

def setup_hg_repo(repo, rev):
    ori_dir = getcwd();
    chdir(repo);
    system("git checkout -f " + rev);
    system("git clean -f -d");
    chdir(ori_dir);

def build_repo(repo, build_cmd):
    cmd = build_cmd + " " + repo;
    system(cmd);

def test_case(repo, test_dir, work_dir, test_cmd, i):
    ret = set();
    print "Testing: ", i,
    cmd = test_cmd + " " + repo + " " + test_dir + " " + work_dir + " " + str(i) + " > __res";
    #print cmd;
    system(cmd);
    f = open("__res", "r");
    line = f.readline();
    f.close();
    s = line.strip();
    if (s != ""):
        v = int(s);
        assert(v == i);
        ret.add(v);
        print "PASS";
    else:
        print "FAIL";
    system("rm -rf __res");
    return ret;

def test_repo(repo, test_dir, work_dir, test_cmd):
    ret = set();
    for i in range(1, 62):
        a = test_case(repo, test_dir, work_dir, test_cmd, i);
        ret = ret | a;
    return ret;

build_cmd = argv[1];
test_cmd = argv[2];
src_dir = argv[3];
test_dir = argv[4];
new_rev = argv[5];
if (len(argv) < 7):
    old_rev = new_rev + "^1";
else:
    old_rev = argv[6];
out_file = "wireshark-rev-" + old_rev + "-" + new_rev + ".txt";

work_dir = "__tmp_" + new_rev;
system("mkdir " + work_dir);

repo1 = work_dir + "/tmp1";
repo2 = work_dir + "/tmp2";
tmp_test_dir = work_dir + "/tests";
system("cp -rf " + src_dir + " " + repo1);
system("cp -rf " + src_dir + " " + repo2);
system("cp -rf " + test_dir + " " + tmp_test_dir);
setup_hg_repo(repo1, new_rev);
setup_hg_repo(repo2, old_rev);

build_repo(repo1, build_cmd);
build_repo(repo2, build_cmd);

s1 = test_repo(repo1, tmp_test_dir, work_dir, test_cmd);
s2 = test_repo(repo2, tmp_test_dir, work_dir, test_cmd);
diff12 = s1 - s2;
diff21 = s2 - s1;
common = s1 & s2;
fout = open(out_file, "w");
print >>fout, "-";
print >>fout, "-";
outdiff = [];
for i in diff12:
    bad = False;
    for j in range(0, 5):
        a = test_case(repo1, tmp_test_dir, work_dir, test_cmd, i);
        b = test_case(repo2, tmp_test_dir, work_dir, test_cmd, i);
        if (len(a) != 1):
            bad = True;
            break;
        if (len(b) != 0):
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

system("rm -rf " + work_dir);
