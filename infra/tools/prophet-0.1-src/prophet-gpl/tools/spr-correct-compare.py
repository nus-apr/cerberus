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
from os import system
import os
import getopt
from sys import argv, exit

t_cases = [
    ("php", "f455f8^1-f455f8", "php"),
    ("php", "1e91069", "php"),
    ("php", "09273098521913a", "php"),
    ("php", "1d984a7", "php"),
    ("php", "991ba131", "php"),
    ("php", "2adf58", "php"),
    ("php", "5a8c917", "php"),
    ("php", "8ba00176", "php"),
    ("php", "1056c57f", "php"),
    ("libtiff", "tests-eec7ec0", "libtiff"),
    ("gmp", "13421", "all"),
    ("gzip", "f17cbd13a1d0a7", "all"),
    ("python", "69784", "python"),
    ("php", "b84967d", "php"),
    ("php", "3acdca", "php"),
    ("php", "efcb9a71", "php"),
    ("php", "ee83270", "php"),
    ("libtiff", "tests2-3edb9cd", "libtiff"),
    ("libtiff", "tests-2e42d63f", "libtiff"),
    ("lighttpd", "2662", "all"),
    ("fbc", "5459", "all"),
    ("lighttpd", "1914", "all"),
    ("python", "70059-70056", "python"),
    ("python", "69935", "python"),
    ("gmp", "14167", "all")
#    ("libtiff", "tests-eec7ec0", "libtiff")
];

def extract_score(line):
    newline = line.strip();
    idx = newline.rfind(" ");
    assert( idx != -1);
    return (newline[0:idx].strip(), float(newline[idx:].strip()));

def normalize(s):
    idx = s.find("abst_hole");
    if (idx != -1):
        idx1 = s.find("(", idx);
        idx2 = idx1 + 1;
        cnt = 1;
        last_idx = idx2;
        tokens = set();
        while (cnt != 0):
            if s[idx2] == "(":
                cnt = cnt + 1;
            if s[idx2] == ")":
                cnt = cnt - 1;
            if (cnt == 1) and (s[idx2] == ","):
                tokens.add(s[last_idx:idx2].strip());
                last_idx = idx2 + 1;
            idx2 = idx2 + 1;
        if (s[last_idx:idx2-1].strip() != ""):
            tokens.add(s[last_idx:idx2-1].strip());
        return (s[0:idx] + "abst_hole(" + s[idx2:], tokens);
    return (s, set());

def check(lines1, lines2, score_d, priority):
    if (len(lines1) < len(lines2)):
        return (False, 0.0);
    abst_key = "NULL";
    for i in range(0, len(lines2)):
        (a, tokena) = normalize(lines1[i].strip());
        (b, tokenb) = normalize(lines2[i].strip());
        assert( len(tokenb) < 2);
        if (len(tokenb) == 1):
            abst_key = list(tokenb)[0];
        if (a != b):
            return (False, 0.0);
        for token in tokenb:
            if not token in tokena:
                return (False, 0.0);
    return (True, priority);

(opts, args) = getopt.getopt(argv[1:], "", ["bugfile", "nloc=", "replace-ext", "cond-ext"]);
nof = True;
nloc = 200;
replace_ext = False;
cond_ext = False;
for o, a in opts:
    if o == "--bugfile":
        nof = False;
    if o == "--nloc":
        nloc = int(a);
    if o == "--replace-ext":
        replace_ext = True;
    if o == "--cond-ext":
        cond_ext = True;

cur_dir = os.path.abspath(os.path.dirname(argv[0]));
prophet_cmd = cur_dir + "/../build/src/prophet";
build_test_dir = cur_dir +"/../build/tests";
test_dir = cur_dir + "/../tests";
feature_dir = cur_dir + "/../crawler";
passed_cnt = 0;
failed_cnt = 0;
cumu_ratio = 0.0;
system("rm -rf __tmp.log");

for app, case, feature in t_cases:
    if (not os.path.exists(build_test_dir + "/" + app + "-case-" + case)):
        print "Scenario not found, Skiped: " + app + "-" + case;
        continue;
    app_ref_file = test_dir + "/" + app + "-cases/" + case + ".exp";
    system("rm -rf __tmp.res");
    cmd = prophet_cmd + " -blowup -r " + build_test_dir + "/" + app + "-case-" + case + "/" + \
        app + "-" + case + "-workdir -skip-verify";
    if (nof):
        cmd += " -consider-all -first-n-loc " + str(nloc);
    if (replace_ext):
        cmd += " -replace-ext";
    if (cond_ext):
        cmd += " -cond-ext";
    cmd += " -print-fix-only __tmp.res >>__tmp.log 2>&1";
    # print "Invoking cmd: " + cmd;
    ret = system(cmd);
    if (ret != 0):
        print "Failed: " + app + "-" + case;
        failed_cnt += 1;
        continue;

    refs = [];

    fin = open(app_ref_file, "r");
    ref_lines = fin.readlines();
    fin.close();
    x = len(ref_lines);
    while (x > 0):
        if (ref_lines[x - 1].strip() == ""):
            x -= 1;
        else:
            break;
    refs.append(ref_lines[0:x]);
    i = 2;
    while (os.path.exists(app_ref_file + str(i))):
        fin = open(app_ref_file + str(i), "r");
        ref_lines = fin.readlines();
        fin.close();
        x = len(ref_lines);
        while (x > 0):
            if (ref_lines[x - 1].strip() == ""):
                x -= 1;
            else:
                break;
        refs.append(ref_lines[0:x]);
        i += 1;

    fin = open("__tmp.res", "r");
    out_lines = fin.readlines();
    fin.close();

    one_case = [];
    i = 0;
    candidate_cnt = 0;
    schema_cnt = 0;
    score_l = [];
    found = False;
    res_score = -1e20;
    res_schema_cnt = 0;
    while i < len(out_lines):
        line = out_lines[i];
        if line[0:5] == "=====":
            schema_cnt += 1;
            score_d = {};
            tmp_tokens = one_case[0].strip().split();
            assert( len(tmp_tokens) > 0)
            blowup_cnt = int(tmp_tokens[len(tmp_tokens) - 1]);
            (_, priority) = extract_score(one_case[1]);

            case_to_check = one_case[2:];
            candidate_num = 1;
            for the_line in case_to_check:
                (_, tokena) = normalize(the_line.strip());
                if (candidate_num < len(tokena) + 1):
                    candidate_num = len(tokena) + 1;
            for j in range(1, candidate_num + 1):
                score_l.append((priority, schema_cnt));
            candidate_cnt += candidate_num;

            for ref_lines in refs:
                (ret, match_s) = check(case_to_check, ref_lines, score_d, priority);
                if ret:
                    found = True;
                    if res_score < match_s:
                        res_score = match_s;
                        res_schema_cnt = schema_cnt;
                        res_blowup_cnt = blowup_cnt;
            one_case = [];
        else:
            one_case.append(line);
        i += 1;

    if found:
        print "Found " + app + "-" + case;
        print "Total schema " + str(schema_cnt);
        print "Correct at schema " + str(res_schema_cnt) + " blowup " + str(res_blowup_cnt) + " ratio " + str(float(res_blowup_cnt + res_schema_cnt)/res_schema_cnt);
    else:
        print "Not found: " + app + "-" + case;

system("rm -rf __tmp.res");
if failed_cnt == 0:
    system("rm -rf __tmp.log");
