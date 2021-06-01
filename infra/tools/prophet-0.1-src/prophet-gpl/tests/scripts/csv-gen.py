#!/usr/bin/env python
from os import system
import csv
import os
from sys import argv

first_row = ["schema", "candidate", "partial_candidate", "correct_rank", "eval_candidate", "eval_partial", "plausible_template", "partial_plausible_template", "plausible_cnt", "partial_plausible_cnt", "correct_cnt", "correct_rank_inp", "correct_rank_inp_template"];

def case_id_convert(mine_id):
    for k in mine_to_public.keys():
        if mine_id.find(k) == 0:
            return mine_to_public[k];
    print mine_to_public;
    print mine_id;
    assert(0);

def init_sheet_d():
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
    sheet["lighttpd-2661-2662"] = {};
    sheet["lighttpd-1913-1914"] = {};
    sheet["python-70056-70059"] = {};
    sheet["python-69934-69935"] = {};
    sheet["gmp-14166-14167"] = {};
    return sheet;

def handle_out_log(fname, sheet, case_token):
    f = open(fname, "r");
    should_track = False;
    track_passed_token = False;
    candidate_pass_cnt = 0;
    partial_candidate_cnt = 0;
    last_count = 0;
    for line in f:
        tokens = line.strip().split();
        if should_track:
            if track_passed_token:
                if len(tokens) == 1 and tokens[0] == "Passed!":
                    candidate_pass_cnt += 1;
            else:
                if len(tokens) == 3:
                    if tokens[0] == "Passed" and tokens[1] == "Positive" and tokens[2] == "Cases":
                        candidate_pass_cnt += 1;
        if len(tokens) == 5:
            if (tokens[2] == "different") and (tokens[3] == "repair") and (tokens[4] == "schemas!!!!"):
                sheet[case_token]["schema"] = tokens[1];
        if len(tokens) == 8:
            if (tokens[2] == "different") and (tokens[3] == "repair") and (tokens[4] == "candidate")\
                    and (tokens[5] == "templates"):
                sheet[case_token]["candidate"] = tokens[1];
        if len(tokens) == 6:
            if (tokens[0] == "The") and (tokens[1] == "number") and (tokens[2] == "of") and \
                    (tokens[3] == "explored") and (tokens[4] == "templates:"):
                sheet[case_token]["eval_candidate"] = tokens[5];
                count = int(tokens[5]);
                if (count - last_count > 1):
                    partial_candidate_cnt += count - last_count;
                last_count = count;

        if len(tokens) > 1:
            if tokens[0] == "BasicTester,":
                should_track = True;
                track_passed_token = False;
            if tokens[0] == "CondTester,":
                if line.find("Postprocessing") != -1:
                    should_track = True;
                    track_passed_token = True;
                else:
                    should_track = False;
                    track_passed_token = False;
            if tokens[0] == "StringConstTester":
                if line.find("postprocessing!") != -1:
                    should_track = True;
                    track_passed_token = False;
                else:
                    should_track = False;
                    track_passed_token = False;
            if tokens[0] == "StringConstTester,":
                should_track = False;
                track_passed_token = False;

    f.close();
    #sheet[case_token]["candidate_pass_cnt"] = candidate_pass_cnt;
    sheet[case_token]["eval_partial"] = partial_candidate_cnt;

def handle_space_log(fname, sheet, sheet_type_token):
    f = open(fname, "r");
    last_passed = False;
    case_id = "";
    for line in f:
        tokens = line.strip().split();
        if len(tokens) == 0:
            continue;
        if tokens[0] == "Passed":
            case_id = case_id_convert(tokens[1]);
            last_passed = True;
        elif last_passed:
            idx = tokens[3].find("/");
            assert( idx != -1);
            # quick fix for the condition extension off cases
            if (case_id == "lighttpd-1913-1914" or case_id == "python-70056-70059") and (sheet_type_token.find("cext") == -1):
                sheet[case_id]["correct_rank"] = "";
            else:
                sheet[case_id]["correct_rank"] = tokens[3][0:idx];
            last_passed = False;
        else:
            last_passed = False;
    f.close();

def parse_block(line):
    tokens = line.strip().split();
    return int(tokens[len(tokens) - 1]);

def handle_check_log(fname, sheet, sheet_type):
    f = open(fname, "r");
    current_case = "";
    lines = f.readlines();
    f.close();
    cnt_helper = 2;
    for line in lines:
        cnt_helper += 1;
        tokens = line.strip().split();
        if len(tokens) == 2:
            if tokens[0] == "Case:":
                mine_id = tokens[1][0:len(tokens[1]) - 1];
                current_case = case_id_convert(mine_id);
                continue;
        if len(tokens) == 4:
            if (tokens[0] == "Total") and (tokens[1] == "parsed") \
                    and (tokens[3] == "candidates"):
                sheet[current_case]["plausible_cnt"] = tokens[2];
                cnt_helper = 0;
                continue;
        if cnt_helper == 1:
            correct_cnt = 0;
            for token in tokens:
                if len(token) > 0:
                    if token[len(token) - 1] == "*":
                        correct_cnt += 1;
            if ((current_case == "lighttpd-1913-1914") or \
                    (current_case == "python-70056-70059")) and\
                    (sheet_type.find("cext") == -1):
                correct_cnt = 0;
            if (current_case == "libtiff-d13be72c-ccadf48a") and \
                    (sheet_type.find("cext") != -1):
                if correct_cnt > 0:
                    correct_cnt += 1;
            sheet[current_case]["correct_cnt"] = str(correct_cnt);
            continue;
        elif cnt_helper == 2:
            blocks = line.strip().split("\t");
            if len(blocks) < 7:
                continue;
            # assert( len(blocks) >= 7);
            sheet[current_case]["partial_candidate"] = parse_block(blocks[1]);
            sheet[current_case]["partial_plausible_cnt"] = parse_block(blocks[2]);
            sheet[current_case]["plausible_template"] = parse_block(blocks[3]);
            sheet[current_case]["partial_plausible_template"] = parse_block(blocks[4]);
            sheet[current_case]["correct_rank_inp"] = parse_block(blocks[6]);
            sheet[current_case]["correct_rank_inp_template"] = parse_block(blocks[5]);

def handle_out_res(fname, sheet, case_token):
    f = open(fname, "r");
    lines = f.readlines();
    f.close();
    tokens = lines[0].strip().split();
    if (int(tokens[0]) > 5000):
        sheet[case_token]["correct_rank_inp"] = "-";
    else:
        sheet[case_token]["correct_rank_inp"] = tokens[0];

mine_to_public = {};
current_cwd = os.path.abspath(os.path.dirname(argv[0]));
with open(current_cwd + "/nameref.csv", "rU") as fin:
    reader = csv.reader(fin);
    for row in reader:
        did = row[0] + "-" + row[1];
        mine_id = row[2][0:len(row[2]) - 7];
        if mine_id != "":
            mine_to_public[mine_id] = did;

print mine_to_public;

table_to_d = {};
assert( len(argv) > 2);
in_dir = argv[1];
out_dir = argv[2];

if not os.path.exists(out_dir):
    system("mkdir " + out_dir);

for root, dirs, files in os.walk(in_dir):
    for fname in files:
        if fname.find(".tar.gz") != -1:
            continue;
        idx = fname.find("-");
        if idx == -1:
            continue;
        type_token = fname[0:idx];
        sys_idx = fname.find("-spr-");
        if sys_idx == -1:
            sys_idx = fname.find("-prophet-");
        if sys_idx == -1:
            continue;
        dot_idx = fname.find("-fdump.");
        if dot_idx == -1:
            dot_idx = fname.find(".");
        if dot_idx == -1:
            continue;
        sheet_type_token = fname[sys_idx + 1: dot_idx];
        if sheet_type_token in table_to_d:
            sheet = table_to_d[sheet_type_token];
        else:
            sheet = init_sheet_d();
            table_to_d[sheet_type_token] = sheet;
        if type_token == "out":
            case_token = fname[idx+1:sys_idx];
            handle_out_log(root + "/" + fname, sheet, case_token);
        elif type_token == "space":
            handle_space_log(root + "/" + fname, sheet, sheet_type_token);
        elif type_token == "res":
            continue;
#            case_token = fname[idx+1:sys_idx];
#            handle_out_res(root + "/" + fname, sheet, case_token);
        else:
            assert(type_token == "check");
            handle_check_log(root + "/" + fname, sheet, sheet_type_token);

for type_token in table_to_d.keys():
    with open(out_dir + "/" + type_token + ".csv", "w") as csvf:
        csvwriter = csv.writer(csvf);
        csvwriter.writerow([""] + first_row);
        sheet = table_to_d[type_token];
        for case_id in sheet.keys():
            the_row = [case_id];
            for row_token in first_row:
                if row_token in sheet[case_id]:
                    # This is an ugly fix
                    if row_token == "correct_rank_inp":
                        if sheet[case_id][row_token] == "-" and "correct_cnt" in sheet[case_id] and sheet[case_id]["correct_cnt"] != "0":
                            the_row.append("?");
                            continue;
                    the_row.append(sheet[case_id][row_token]);
                else:
                    the_row.append("");
            csvwriter.writerow(the_row);
