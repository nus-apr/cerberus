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
from os import system, chdir, getcwd
from sys import argv
import subprocess

build_cmd = argv[1];
dep_dir = argv[2];
src_dir = argv[3];
test_dir = argv[4];
rev = argv[5];
if (len(argv) < 7):
    out_dir = test_dir + "-" + rev;
else:
    out_dir = argv[6];

work_dir = "__tmp" + rev;
system("cp -rf " + src_dir + " " + work_dir);

ori_dir = getcwd();
chdir(work_dir);
system("git checkout -f " + rev);
system("git clean -f -d");
chdir(ori_dir);
system(build_cmd + " -p " + dep_dir + " " + work_dir);

system("mv " + work_dir + "/test " + work_dir+"/ori_test");
system("cp -rf " + test_dir + " " + work_dir + "/test");
chdir(work_dir + "/test");
system("GENEXPOUT=1 CMPEXPOUT=0 make check");
chdir(ori_dir);

print "Goint to generate testdir for revision " + rev + " case: " + out_dir;
system("cp -rf " + test_dir + " " + out_dir);
system("cp -rf " + work_dir + "/test/*.exp " + work_dir + "/test/*.tol " + out_dir+"/");
system("rm -rf " + work_dir);
