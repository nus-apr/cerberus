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
#    ("python", "69784", "python"),
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
];

use_spr_priority = False;

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

def check(lines1, lines2, score_d, priority, determined_abstv = ""):
    if (len(lines1) != len(lines2)):
        return (False, 0.0, "");
    abst_key = "NULL";
    if determined_abstv != "":
        abst_key = determined_abstv;
    for i in range(0, len(lines2)):
        (a, tokena) = normalize(lines1[i].strip());
        (b, tokenb) = normalize(lines2[i].strip());
        if determined_abstv == "":
            assert( len(tokenb) < 2);
            if (len(tokenb) == 1):
                abst_key = list(tokenb)[0];
        if (a != b):
            return (False, 0.0, "");
        if determined_abstv == "":
            for token in tokenb:
                if not token in tokena:
                    return (False, 0.0, "");
        else:
            if abst_key != "NULL" and lines1[i].find("abst_hole") != -1:
                if not abst_key in tokena:
                    return (False, 0.0, "");
    if use_spr_priority:
        return (True, priority, abst_key);
    else:
        return (True, score_d[abst_key], abst_key);

(opts, args) = getopt.getopt(argv[1:], "o:", ["spr", "loc-only", "geop=", "nloc=", "no-sema", "random", "no-mod", "replace-ext", "cond-ext", "ssvm"]);
use_loc_only = False;
use_geop = False;
no_sema = False;
use_spr_priority = False;
no_mod = False;
use_random = False;
replace_ext = False;
cond_ext = False;
ssvm = False;
nof_lookup = 200;

cur_dir = os.path.abspath(os.getcwd());
prophet_cmd = cur_dir + "/../build/src/prophet";
build_test_dir = cur_dir +"/../build/tests";
test_dir = cur_dir + "/../tests";
feature_dir = cur_dir + "/../crawler";
out_csv_file = "";

for o, a in opts:
    if o == "--spr":
        use_spr_priority = True;
    if o == "--loc-only":
        use_loc_only = True;
    if o == "--geop":
        use_geop = True;
        geop = a;
    if o == "--nloc":
        nof_lookup = int(a);
    if o == "--no-sema":
        no_sema = True;
    if o == "--no-mod":
        no_mod = True;
    if o == "-o":
        out_csv_file = a;
    if o == "--random":
        use_spr_priority = True;
        use_random = True;
    if o == "--replace-ext":
        replace_ext = True;
    if o == "--cond-ext":
        cond_ext = True;
    if o == "--ssvm":
        ssvm = True;

if (use_spr_priority and use_loc_only):
    print "invalid arguments!";
    exit(1);

system("rm -rf __tmp.log");
candidate_result_dir = args[0];
csv_plausible = [];
csv_correct = [];
case_cnt = 0;

for app, case, feature in t_cases:
    case_cnt += 1;
    print "Case: " + app + "-" + case + ":";
    case_tar_ball = candidate_result_dir + "/" + app + "-" + case + ".tar.gz";
    if (not os.path.exists(case_tar_ball)):
        print "Cannot find the case: " + app + "-" + case;
        continue;

    if (not os.path.exists(build_test_dir + "/" + app + "-case-" + case)):
        print "Scenario not found, Skip: " + app + "-" + case;
        continue;

    app_ref_file = test_dir + "/" + app + "-cases/" + case + ".exp";
    system("rm -rf __tmp.res");
    cmd = prophet_cmd + " -r " + build_test_dir + "/" + app + "-case-" + case + "/" + \
        app + "-" + case + "-workdir -skip-verify";
    if nof_lookup != 0:
        cmd += " -consider-all -first-n-loc " + str(nof_lookup);
    if not use_spr_priority and not use_loc_only:
        if no_sema:
            cmd += " -feature-para " + feature_dir + "/para-no-sema-" + feature + ".out";
        elif no_mod:
            cmd += " -feature-para " + feature_dir + "/para-no-mod-" + feature + ".out";
        elif replace_ext:
            cmd += " -feature-para " + feature_dir + "/para-rext-" + feature + ".out";
        elif ssvm:
            cmd += " -feature-para " + feature_dir + "/para-ssvm-" + feature + ".out";
        else:
            cmd += " -feature-para " + feature_dir + "/para-" + feature + ".out";
    elif use_loc_only and not use_spr_priority:
        cmd += " -no-feature ";
    if (use_geop):
        cmd += " -geop " + geop;
    if replace_ext:
        cmd += " -replace-ext";
    if cond_ext:
        cmd += " -cond-ext";
    cmd += " -print-fix-only __tmp.res >>__tmp.log 2>&1";
    # print "Invoking cmd: " + cmd;
    ret = system(cmd);
    if (ret != 0):
        print "Failed to run cmd: " + cmd;
        exit(1);

    correct_refs = [];

    fin = open(app_ref_file, "r");
    ref_lines = fin.readlines();
    fin.close();
    x = len(ref_lines);
    while (x > 0):
        if (ref_lines[x - 1].strip() == ""):
            x -= 1;
        else:
            break;
    correct_refs.append(ref_lines[0:x]);
    i = 2;
    while (os.path.exists(app_ref_file + str(i))):
        fin = open(app_ref_file + str(i), "r");
        ref_lines = fin.readlines();
        x = len(ref_lines);
        while (x > 0):
            if (ref_lines[x - 1].strip() == ""):
                x -= 1;
            else:
                break;
        fin.close();
        correct_refs.append(ref_lines[0:x]);
        i += 1;

    system("rm -rf __plausible");
    system("mkdir __plausible");
    system("cp " + case_tar_ball + " __plausible/");
    system("cd __plausible && tar xzf " + app + "-" + case + ".tar.gz");

    plausible_refs = [];
    i = 0;
    candidate_ref_file =  "__plausible/__candidate";
    while (os.path.exists(candidate_ref_file + "-" + str(i) + ".txt")):
        fin = open(candidate_ref_file + "-" + str(i) + ".txt", "r");
        first_line = fin.readline();
        tokens = first_line.strip().split();
        score = float(tokens[1]);
        second_line = fin.readline();
        tokens = second_line.strip().split();
        var_str = tokens[1];
        ref_lines = fin.readlines();
        x = len(ref_lines);
        while (x > 0):
            if (ref_lines[x - 1].strip() == ""):
                x -= 1;
            else:
                break;
        fin.close();
        plausible_refs.append((score, var_str, ref_lines[1: x]));
        i += 1;
    print "Total parsed " + str(i) + " candidates";
    system("rm -rf __plausible");

    score_collect = [];

    fin = open("__tmp.res", "r");
    out_lines = fin.readlines();
    fin.close();

    one_case = [];
    i = 0;
    candidate_cnt = 0;
    partial_candidate_cnt = 0;
    schema_cnt = 0;
    score_l = [];
    res_score = -1e20;
    res_schema_cnt = 0;
    marked_refs = set();
    while i < len(out_lines):
        line = out_lines[i];
        if line[0:5] == "=====":
            schema_cnt += 1;
            score_d = {};
            (_, priority) = extract_score(one_case[1]);
            is_partial = False;
            if use_spr_priority:
                x = len(one_case);
                if (use_random):
                    x = len(one_case) - 1;
                    (_, priority) = extract_score(one_case[x]);
                while (x > 0):
                    if one_case[x - 1].strip() == "":
                        x -= 1;
                    else:
                        break;
                case_to_check = one_case[2:x];
                candidate_num = 1;
                tokena = [];
                for the_line in case_to_check:
                    if the_line.find("abst_hole") != -1:
                        idx = the_line.find("abst_hole");
                        idx1 = the_line.find("(", idx);
                        idx2 = idx1 + 1;
                        pcnt = 1;
                        last_idx = idx2;
                        while (pcnt != 0):
                            if the_line[idx2] == "(":
                                pcnt = pcnt + 1;
                            if the_line[idx2] == ")":
                                pcnt = pcnt - 1;
                            if (pcnt == 1) and (the_line[idx2] == ","):
                                tokena.append(the_line[last_idx:idx2].strip());
                                last_idx = idx2 + 1;
                            idx2 = idx2 + 1;
                        if (the_line[last_idx:idx2-1].strip() != ""):
                            tokena.append(the_line[last_idx:idx2-1].strip());
                        canddiate_num = len(tokena) + 1;
                        break;
                tmp_set = set();
                # for NULL
                score_l.append((priority, schema_cnt, 0));
                candidate_cnt += 1;
                for j in range(0, len(tokena)):
                    if not tokena[j] in tmp_set:
                        tmp_set.add(tokena[j]);
                        score_l.append((priority, schema_cnt, j + 1));
                        candidate_cnt += 1;
                        # I hate this fucking code
                        if not is_partial:
                            partial_candidate_cnt += 1;
                        partial_candidate_cnt += 1;
                        is_partial = True;
            else:
                if line.find("Score Detail") != -1:
                    # This is a compound case
                    i += 1;
                    icnt = 0;
                    while i < len(out_lines):
                        score_line = out_lines[i];
                        if score_line[0:5] == "=====":
                            break;
                        (vstr, fs) = extract_score(score_line);
                        if not vstr in score_d:
                            score_d[vstr] = fs;
                            icnt += 1;
                            score_l.append((fs, schema_cnt, icnt));
                        i += 1;
                else:
                    if not use_spr_priority:
                        (vstr, fs) = extract_score(one_case[len(one_case) - 1]);
                        score_d["NULL"] = fs;
                        score_l.append((fs, schema_cnt, 0));
                x = len(one_case) - 1;
                while (x > 0):
                    if one_case[x - 1].strip() == "":
                        x -= 1;
                    else:
                        break;
                case_to_check = one_case[2:x];
                candidate_cnt += len(score_d);
                is_partial = (len(score_d) > 1);
                if is_partial:
                    partial_candidate_cnt += len(score_d);

            found_vstr_map = {};
            found_vstr_map_cnt = {};
            for idx in range(len(plausible_refs)):
                (score, var_str, ref_lines ) = plausible_refs[idx];
                (ret, match_s, _) = check(case_to_check, ref_lines, score_d, priority, var_str);
                vscore = score;
                if use_spr_priority:
                    vscore = match_s;
                if ret:
                    if not var_str in found_vstr_map:
                        found_vstr_map[var_str] = vscore;
                        if not idx in marked_refs:
                            found_vstr_map_cnt[var_str] = 1;
                        else:
                            found_vstr_map_cnt[var_str] = 0;
                    else:
                        if not idx in marked_refs:
                            found_vstr_map_cnt[var_str] += 1;
                        if found_vstr_map[var_str] < vscore:
                            found_vstr_map[var_str] = vscore;
                    marked_refs.add(idx);

            if len(found_vstr_map) > 0:
                correct_keys = set();
                for ref_lines in correct_refs:
                    (ret, match_s, abst_key) = check(case_to_check, ref_lines, score_d, priority);
                    if ret:
                        correct_keys.add(abst_key);
                for key in found_vstr_map.keys():
                    key_id = 0;
                    if use_spr_priority:
                        for xx in range(0, len(tokena)):
                            if tokena[xx] == key:
                                key_id = xx + 1;
                                break;
                    if key in correct_keys:
                        score_collect.append((idx, 1, found_vstr_map[key], schema_cnt, key_id, is_partial, found_vstr_map_cnt[key]));
                    else:
                        score_collect.append((idx, 0, found_vstr_map[key], schema_cnt, key_id, is_partial, found_vstr_map_cnt[key]));

            one_case = [];
        else:
            one_case.append(line);
        i += 1;

    assert(candidate_cnt == len(score_l));
    ranks = [];
    rank_tmp_set = set();
    score_collect.sort();

    for _, is_correct, res_score, res_schema_cnt, res_id, is_partial, volumn in score_collect:
        rank = 1;
        for s, cnt, idcnt in score_l:
            if (s > res_score) or ((s == res_score) and (cnt < res_schema_cnt)) or ((s == res_score) and (cnt == res_schema_cnt) and (idcnt < res_id) and (use_spr_priority)):
                rank += 1;
        while rank in rank_tmp_set:
            rank += 1;
        rank_tmp_set.add(rank);
        ranks.append((rank, is_correct, is_partial, volumn));

    ranks.sort();
    cnt = 0;
    volumn_cnt = 0;
    partial_cnt = 0;
    first_correct = 0;
    first_correct_volumn = 0;
    partial_volumn_cnt = 0;
    for rank, is_correct, is_partial, volumn in ranks:
        cnt += 1;
        volumn_cnt += volumn;
        if is_partial:
            partial_cnt += 1;
            partial_volumn_cnt += volumn;
        if is_correct:
            print "(" + str(volumn) + "," + str(rank)+")*",
            if (first_correct == 0):
                first_correct = cnt;
                first_correct_volumn = volumn_cnt - volumn + 1;
            csv_correct.append( (case_cnt, float(rank) / candidate_cnt) );
        else:
            print "(" + str(volumn) + "," + str(rank) +")",
            csv_plausible.append( (case_cnt, float(rank) / candidate_cnt) );
    print;
    print "Space size: " + str(candidate_cnt) + "\tPartialSize: " + str(partial_candidate_cnt) + "\tPartialParsed: " + str(partial_volumn_cnt) + "\tPlausible: " + str(len(ranks)) + "\tPartialPlau: " + \
        str(partial_cnt) + "\tFirst correct in plausible: " + str(first_correct) + "\tFirst correct in all: " + str(first_correct_volumn);
    print;

system("rm -rf __tmp.res");
system("rm -rf __tmp.log");

if out_csv_file != "":
    fout = open(out_csv_file, "w");
    total = len(csv_plausible);
    if total < len(csv_correct):
        total = len(csv_correct);
    for i in range(0, total):
        if i < len(csv_plausible):
            print >> fout, csv_plausible[i][0],
        print >> fout, ",",
        if i < len(csv_plausible):
            print >> fout, csv_plausible[i][1],
        print >> fout, ",",
        if i < len(csv_correct):
            print >> fout, csv_correct[i][0],
        print >> fout, ",",
        if i < len(csv_correct):
            print >> fout, csv_correct[i][1],
        print >> fout;
    fout.close();
