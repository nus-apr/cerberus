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

from os import system, getcwd, chdir
from sys import argv

assert( len(argv) > 3);
top_build_dir = argv[1];
top_src_dir = argv[2];
case_str = argv[3];

tokens = case_str.split("-");
if len(tokens) == 2:
    test_dir = tokens[0];
    new_rev = tokens[1];
    old_rev = tokens[1] + "^1";
else:
    assert( len(tokens) == 3);
    test_dir = tokens[0];
    new_rev = tokens[1];
    old_rev = tokens[2];

out_dir = getcwd() + "/libtiff-case-" + case_str;
system("mkdir " + out_dir);

system("cp -rf " + top_build_dir + "/benchmarks/libtiff-src " + out_dir + "/libtiff-src");
ori_dir = getcwd();
chdir(out_dir + "/libtiff-src");
system("git checkout -f " + old_rev);
chdir(ori_dir);

cmd = top_src_dir + "/tools/libtiff-prepare-test.py " + top_src_dir + "/tools/libtiff-build.py " + \
    top_build_dir + "/benchmarks/libtiff-deps " + \
    top_build_dir + "/benchmarks/libtiff-src " + top_build_dir + "/benchmarks/libtiff-" + test_dir + \
    " " + new_rev + " " + out_dir + "/libtiff-test";
print cmd;
system(cmd);

cmd = top_src_dir + "/tools/libtiff-rev-test.py " + top_src_dir + "/tools/libtiff-build.py " + \
    top_src_dir + "/tools/libtiff-test.py " + top_build_dir + "/benchmarks/libtiff-src " + \
    out_dir+"/libtiff-test " + new_rev + " " + old_rev + " " + top_build_dir + "/benchmarks/libtiff-deps";
system(cmd);
system("cp -f libtiff-rev-" + new_rev +".txt " + out_dir+"/libtiff-"+case_str + ".revlog");
system("rm -f libtiff-rev-" + new_rev +".txt");

f = open(top_src_dir + "/benchmarks/libtiff-bug-file.log");
lines = f.readlines();
f.close();
d = {};
for line in lines:
    token = line.strip().split();
    if (len(token) < 2):
        continue;
    d[token[0]] = token[1];

print "Creating conf file for " + case_str + "...";
f = open(out_dir + "/libtiff-" + case_str + ".conf", "w");
print >>f, "revision_file=" + out_dir + "/libtiff-" + case_str + ".revlog";
print >>f, "src_dir=" + out_dir + "/libtiff-src";
print >>f, "test_dir=" + out_dir + "/libtiff-test";
print >>f, "dep_dir=" + top_build_dir + "/benchmarks/libtiff-deps";
print >>f, "build_cmd=" + top_src_dir + "/tools/libtiff-build.py";
print >>f, "test_cmd=" + top_src_dir + "/tools/libtiff-test.py";
print >>f, "localizer=profile";
print >>f, "bugged_file=" + d[case_str];
print >>f, "fixed_out_file=libtiff-fix-" + case_str + ".c";
print >>f, "single_case_timeout=10";
f.close();

print "Creating workdir for " + case_str + "...";
system("time " + top_build_dir + "/src/prophet " + out_dir + "/libtiff-" + case_str + ".conf -r " + \
       out_dir + "/libtiff-" + case_str +"-workdir -init-only");
