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

assert( len(argv) > 3 );
top_build_dir = argv[1];
top_src_dir = argv[2];
case_str = argv[3];
idx = case_str.find("-");
if idx == -1:
    new_rev = case_str;
    old_rev = str(int(new_rev) - 1);
else:
    new_rev = case_str[0:idx];
    old_rev = case_str[idx+1:];

out_dir = getcwd() + "/python-case-" + case_str;
system("mkdir " + out_dir);

print "Creating revision log for " + case_str + "...";
cmd = top_src_dir + "/tools/python-rev-test.py " + top_src_dir + "/tools/python-build.py " + \
    top_src_dir + "/tools/python-test.py " + top_build_dir + "/benchmarks/python-src " + \
    top_build_dir + "/benchmarks/python-tests " + new_rev + " " + old_rev;

system(cmd);
system("cp -f python-rev-" + old_rev + "-" + new_rev + ".txt " + \
       out_dir + "/python-" + case_str + ".revlog");
system("rm -f python-rev-" + old_rev + "-" + new_rev + ".txt");

f = open(top_src_dir + "/benchmarks/python-bug-file.log");
lines = f.readlines();
f.close();
d = {};
for line in lines:
    token = line.strip().split();
    if (len(token) != 2):
        continue;
    d[token[0]] = token[1];

print "Creating conf file for " + case_str + "...";
f = open(out_dir + "/python-" + case_str + ".conf", "w");
print >> f, "revision_file=" + out_dir + "/python-" + case_str + ".revlog";
system("cp -rf " + top_build_dir + "/benchmarks/python-src " + out_dir + "/python-src");
ori_dir = getcwd();
chdir(out_dir + "/python-src");
system("hg update -r " + old_rev + " -C");
chdir(ori_dir);
print >> f, "src_dir=" + out_dir + "/python-src";
print >> f, "test_dir=" + top_build_dir + "/benchmarks/python-tests";
print >> f, "build_cmd=" + top_src_dir + "/tools/python-build.py";
print >> f, "test_cmd=" + top_src_dir + "/tools/python-test.py";
print >> f, "localizer=profile";
print >> f, "bugged_file=" + d[case_str];
print >> f, "fixed_out_file=python-fix-" + case_str + ".c";
f.close();

print "Creating workdir for " + case_str + "...";
system("time " + top_build_dir + "/src/prophet " + out_dir + "/python-" + case_str + ".conf -r " + \
       out_dir + "/python-" + case_str +"-workdir -init-only");
