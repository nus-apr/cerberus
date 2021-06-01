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

def analysis_repair_log(logf):
    f = open(logf, "r");
    mincond = 10000000;
    minbasic = 10000000;
    last_type = 0;
    last_idx = 0;
    for line in f:
        tokens = line.strip().split();
        if (line.find("instance id") != -1):
            s = tokens[len(tokens) - 1];
            idx = int(s[0:len(s) - 1]);
            if (line.find("Postprocessing") != -1):
                last_idx = idx;
                last_type = 1;
            elif (line.find("BasicTester") != -1):
                last_idx = idx;
                last_type = 2;
            else:
                last_idx = 0;
                last_type = 0;
        if (line[0:7] == "Passed!"):
            if (last_type == 1):
                if (mincond > last_idx):
                    mincond = last_idx;
            elif (last_type == 2):
                if (minbasic > last_idx):
                    minbasic = last_idx;
    f.close();
    f = open(logf, "r");
    last_counter = 0;
    if (mincond != 10000000):
        cond_lookup = "instance with id " + str(mincond);
    else:
        cond_lookup = "";
    if (minbasic != 10000000):
        basic_lookup = "instance with id " + str(minbasic);
    else:
        basic_lookup = "";
    print "Basic look up: " + basic_lookup;
    print "Cond look up: " + cond_lookup;

    res = 0;
    for line in f:
        tokens = line.strip().split();
        if (line.find("Total ") == 0):
            print "Total " + tokens[1];
        if (line.find("Counter:") == 0):
            last_counter = int(tokens[len(tokens)-1]);
        if (cond_lookup != ""):
            if (line.find(cond_lookup) != -1) and (line.find("Cond") != -1):
                res = last_counter;
                break;
        if (basic_lookup != ""):
            if (line.find(basic_lookup) != -1) and (line.find("Basic") != -1):
                res = last_counter;
                break;
    f.close();
    print "Result counter is " + str(res);




case_str = argv[1];
tokens = case_str.split("-");
prog = tokens[0];
rev = tokens[2];
if (rev[0:5] == "tests"):
    rev += "-" + tokens[3];
dir_str = case_str;

tar_file = prog + "-" + rev + ".tar.gz"
system("tar cvzf " + tar_file + " " + dir_str + " " + prog + "-fix-" + rev + "* " + "repair.log");
analysis_repair_log("repair.log");
