#!/usr/bin/env python
from os import system
from sys import argv
import os
import csv

sheet = {};
sheet["php-307562-307561"] = {};
sheet["php-307846-307853"] = {};
sheet["php-308734-308761"] = {};
sheet["php-309516-309535"] = {};
sheet["php-309579-309580"] = {};
sheet["php-309892-309910"] = {};
sheet["php-310991-310999"] = {};
sheet["php-311346-311348"] = {};
sheet["libtiff-ee2ce5b7-b5691a5a"] = {};
sheet["gmp-13420-13421"] = {};
sheet["php-307914-307915"] = {};
sheet["php-308262-308315"] = {};
sheet["libtiff-d13be72c-ccadf48a"] = {};
sheet["gzip-a1d3d4019d-f17cbd13a1"] = {};
sheet["fbc-5458-5459"] = {};
sheet["php-309688-309716"] = {};
sheet["php-310011-310050"] = {};
sheet["php-309111-309159"] = {};
sheet["libtiff-5b02179-3dfb33b"] = {};

current_cwd = os.path.abspath(os.path.dirname(argv[0]));
defect_list = [];
d = {};
with open(current_cwd + "/nameref.csv", "rU") as f:
    reader = csv.reader(f);
    for row in reader:
        if (row[2] == ""):
            continue;
        idx = row[2].rfind(".tar.gz");
        token = row[2][0:idx];
        d[token] = row[0] + "-" + row[1];
        defect_list.append(row);

def parseChecklog(fname):
    f = open(fname, "r");
    idx1 = fname.find("-");
    idx2 = fname.find("-", idx1+1);
    systype = fname[idx1+1:idx2];
    lines = f.readlines();
    f.close();
    current_case = "";
    cur_line_cnt = 0;
    for line in lines:
        tokens = line.strip().split();
        if (len(tokens) < 1):
            cur_line_cnt += 1;
            continue;
        if (tokens[0] == "Case:"):
            current_case = tokens[1][0: len(tokens[1]) - 1];
            assert(current_case in d);
            current_case = d[current_case];
            if not (current_case in sheet):
                current_case = "";
            cur_line_cnt = 0;
        else:
            cur_line_cnt += 1;
        if (cur_line_cnt == 1):
            if (current_case == ""):
                continue;
            if (tokens[0] != "Total"):
                current_case = "";
                continue;
            sheet[current_case][systype + "-1plausible"] = int(tokens[2]);
        elif (cur_line_cnt == 2):
            correct_cnt = 0;
            plausible_cnt = 0;
            correct_ranks = "";
            if (current_case == ""):
                continue;
            for token in tokens:
                if token[len(token) - 1] == "*":
                    correct_cnt += 1;
                    correct_ranks += str(plausible_cnt + 1) + "/";
                idx = token.find(",");
                plausible_cnt += int(token[1:idx]);
            sheet[current_case][systype + "-2correct"] = correct_cnt;
            sheet[current_case][systype + "-3correctrank"] = correct_ranks;

def dumpcsv(fname):
    f = open(fname, "w");
    a = list(sheet["gzip-a1d3d4019d-f17cbd13a1"].keys());
    a.sort();
    for x in a:
        print >> f, ",", x,
    print >> f;
    for defect in sheet:
        print >>f, defect,
        for x in a:
            if x in sheet[defect]:
                print >> f, ",", sheet[defect][x],
            else:
                print >> f, ", -",
        print >>f;
    f.close();

for checkfname in argv[2:]:
    parseChecklog(checkfname);

dumpcsv(argv[1]);
