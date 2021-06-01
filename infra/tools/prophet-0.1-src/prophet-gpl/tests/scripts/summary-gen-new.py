#!/usr/bin/env python
import csv
from sys import argv
import os
import getopt

def compute_random_effort_gain(k, n, m):
    assert( n <= m);
    if n == 0:
        if look_at < m:
            effort = float(look_at);
        else:
            effort = m;
        return (effort, 0);
    gain = float(0);
    effort = float(0);
    s = float(1);
    for i in range(1, k + 1):
        effort += float(i) * s * n /(m-i+1);
        s *= float(m-n-i+1)/(m-i+1);
        if n + i > m:
            gain = float(1);
            s = 0;
            break;
    effort += float(look_at) * s;
    gain = 1 - s;
    assert( gain <= 1);
    return (effort, gain);


def parseCSV(sys_name, loc_limit, ext_token, csvfname):
    print csvfname;
    row = [];
    row.append(sys_name);
    row.append(loc_limit);
    row.append(ext_token);
    effort = 0;
    gain = 0;
    effort_random = 0;
    gain_random = 0;
    with open(csvfname, "rU") as csvf:
        csvreader = csv.reader(csvf);
        first_row = True;
        in_space = 0;
        correct = 0;
        plausible = 0;
        plausible_ins = 0;
        timeout = 0;
        timeout_ins = 0;
        avg_space = 0;
        avg_cor_rank = 0;
        plausible_12h_cnt = 0;
        correct_12h_cnt = 0;
        tot_plausible_12h = 0;
        tot_correct_12h = 0;
        to_cnt = 0;
        for csvrow in csvreader:
            if first_row:
                first_row = False;
                continue;
            if disable_php and csvrow[0].find("php") != -1:
                continue;
            if php_only and csvrow[0].find("php") == -1:
                continue;
            candidate_num_token = csvrow[2];
            correct_rank_token = csvrow[4];
            plausible_cnt_token = csvrow[9];
            correct_cnt_token = csvrow[11];
            correct_inp_rank_token = csvrow[12];
            if correct_rank_token != "" and correct_rank_token != "0":
                in_space += 1;
                ins = True;
            else:
                ins = False;
            if correct_inp_rank_token == "1":
                correct += 1;
            elif plausible_cnt_token != "0":
                plausible += 1;
                if ins:
                    plausible_ins += 1;
            else:
                timeout += 1;
                if ins:
                    timeout_ins += 1;
            avg_space += int(candidate_num_token);
            if correct_rank_token != "":
                avg_cor_rank += int(correct_rank_token);
            #if csvrow[0].find("fbc") == -1:
            #    p12h = int(plausible_cnt_token);
            #else:
            p12h = int(plausible_cnt_token);
            c12h = int(correct_cnt_token);
            #if (c12h > p12h):
            #    c12h = p12h;
            #    if (c12h > 0):
            #        correct += 1;
            #        plausible -= 1;
            #        plausible_ins -= 1;
            #    print c12h, p12h, csvfname, csvrow[0];
            if p12h > 0:
                plausible_12h_cnt += 1;
                tot_plausible_12h += p12h;
            if c12h > 0:
                correct_12h_cnt += 1;
                tot_correct_12h += c12h;
                # if p12h > 5:
            if look_at > 0:
                (e, g) = compute_random_effort_gain(look_at, c12h, p12h);
                effort_random += e;
                gain_random += g;
                if c12h > 0 and look_at >= int(correct_inp_rank_token):
                    effort += int(correct_inp_rank_token);
                    gain += 1;
                else:
                    if look_at > p12h:
                        effort += p12h;
                    else:
                        effort += look_at;
            if p12h > 0:
                to_cnt += 1;
        row.append(str(in_space));
        avg_space = float(avg_space) / 24;
        avg_cor_rank = float(avg_cor_rank) / in_space;
        row.append(str(correct));
        row.append(str(plausible) + "(" + str(plausible_ins) + ")");
        row.append(str(timeout) + "(" + str(timeout_ins) + ")");
        row.append("{0:.1f}".format(avg_space));
        row.append("{0:.1f}".format(avg_cor_rank));
        row.append(str(plausible_12h_cnt) + "(" + str(tot_plausible_12h) +")");
        row.append(str(correct_12h_cnt) + "(" + str(tot_correct_12h) + ")");
#        if look_at > 0:
#            effort_random = float(effort_random)/ to_cnt;
#            gain_random = float(gain_random)/to_cnt;
#            effort = float(effort)/to_cnt;
#            gain = float(gain)/to_cnt;
    return (row, effort, gain, effort_random, gain_random);

def dump_tex(rows, outf):
    fout = open(outf, "w");
    print >> fout, "\\small";
    print >> fout, "\\begin{tabular}{|l|c|c|c|c|c|c|c|c|c|c|}";
    print >> fout, "\\hline";
    print >> fout, "\\multirow{2}{*}{\\bf System} & {\\bf Loc.} & {\\bf Space} & \multicolumn{2}{|c|}{\\bf Correct} & {\\bf Plausible} & \\multirow{2}{*}{\\bf Timeout} & {\\bf Space} & {\\bf Correct} & {\\bf Plausible} & {\\bf Correct} \\\\";
    print >> fout, "\\cline{4-5}";
    print >> fout, "    & {\\bf Limit} & {\\bf Extension} & {\\bf In Space} & {\\bf First} & \\& {\\bf Blocked} &                         & {\\bf Size} & {\\bf Rank} & {\\bf in 12h}   &  {\\bf in 12h} \\\\";
    print >> fout, "\\hline";
    row0o = ["SPR", "Prophet"];
    row1o = ["100", "200", "300", "2000"];
    row2o = ["No", "CExt", "RExt", "RExt+CExt"];
    for token0 in row0o:
        for token1 in row1o:
            for token2 in row2o:
                for row in rows:
                    if row[0] == token0 and row[1] == token1 and row[2] == token2:
                        first = True;
                        for token in row:
                            if not first:
                                print >> fout, "& ",
                            print >> fout, token,
                            first = False;
                        print >> fout, "\\\\";
                        print >> fout, "\\hline";
                        break;
    print >> fout, "\\end{tabular}";
    fout.close();

def dump_tex2(d, outf):
    fout = open(outf, "w");
    row1o = ["100", "200", "300", "2000"];
    row2o = ["No", "CExt", "RExt", "RExt+CExt"];
    print >> fout, "\\begin{tabular}{|l|c|c|c|c|}";
    print >> fout, "\\hline";
    print >> fout, "\\multirow{2}{*}{\\textbf{Search Space}} & \\multirow{2}{*}{\\scriptsize \\textbf{SPR}} & \\multirow{2}{*}{\scriptsize \\textbf{Prophet}} & \\textbf{\\scriptsize Random} & \\textbf{\\scriptsize Random} \\\\";
    print >> fout, "& & & \\textbf{\\scriptsize (SPR)} & \\textbf{\scriptsize (Prophet)} \\\\";
    print >> fout, "\\hline";
    for token1 in row1o:
        for token2 in row2o:
            if not (token1, token2) in d:
                continue;
            space_token = token1 + "+" + token2;
            print >>fout, "{\\tiny " + space_token + "} &",
            print >>fout, "{0:.0f}".format(d[(token1, token2)]["SPR"][0]) + " / {0:.0f}".format(d[(token1, token2)]["SPR"][1]) + " &",
            print >>fout, "{0:.0f}".format(d[(token1, token2)]["Prophet"][0]) + " / {0:.0f}".format(d[(token1, token2)]["Prophet"][1]) + " &",
            print >>fout, "{0:.1f}".format(d[(token1, token2)]["SPR+R"][0]) + " / {0:.1f}".format(d[(token1, token2)]["SPR+R"][1]) + " &",
            print >>fout, "{0:.1f}".format(d[(token1, token2)]["Prophet+R"][0]) + " / {0:.1f}".format(d[(token1, token2)]["Prophet+R"][1]) + " \\\\";
#            print >>fout, "{0:.1f}\\%".format(d[(token1, token2)]["SPR"] * 100) + " &",
#            print >>fout, "{0:.1f}\\%".format(d[(token1, token2)]["Prophet"] * 100) + " &",
#            print >>fout, "{0:.1f}\\%".format(d[(token1, token2)]["SPR+R"] * 100) + " &",
#            print >>fout, "{0:.1f}\\%".format(d[(token1, token2)]["Prophet+R"] * 100) + " \\\\";
            print >>fout, "\\hline";
    print >> fout, "\\end{tabular}";
    fout.close();

(opts, args) = getopt.getopt(argv[1:], "", ["dis-php", "php-only", "fmt=", "rank-table="]);
out_fmt = "tex";
disable_php = False;
php_only = False;
look_at = 0;
for o, a in opts:
    if o == "--fmt":
        out_fmt = a;
    if o == "--dis-php":
        disable_php = True;
    if o == "--php-only":
        php_only = True;
    if o == "--rank-table":
        look_at = int(a);
in_dir = args[0];
outf = args[1];

rows = [];
d = {};
for root, dirs, files in os.walk(in_dir):
    for csvfname in files:
        if (csvfname[len(csvfname) - 4:] != ".csv"):
            continue;
        dot_idx = csvfname.find(".");
        if dot_idx == -1:
            continue;
        tokens = csvfname[0:dot_idx].strip().split("-");
        loc_limit = "";
        sys_token = "";
        cext_on = False;
        rext_on = False;
        for token in tokens:
            if token == "cext":
                cext_on = True;
            elif token == "rext":
                rext_on = True;
            elif token == "spr":
                assert( sys_token == "");
                sys_token = "SPR";
            elif token == "prophet":
                assert( sys_token == "");
                sys_token = "Prophet";
            else:
                loc_int = int(token);
                loc_limit = str(loc_int);
                assert( loc_int == 100 or loc_int == 200 or loc_int == 300 or loc_int == 2000);
        if cext_on:
            if rext_on:
                ext_token = "RExt+CExt";
            else:
                ext_token = "CExt";
        elif rext_on:
            ext_token = "RExt";
        else:
            ext_token = "No";
        (row, effort, gain, effort_random, gain_random) = parseCSV(sys_token, loc_limit, ext_token, root + "/" + csvfname);
        if not (loc_limit, ext_token) in d:
            d[(loc_limit, ext_token)] = {};
        d[(loc_limit, ext_token)][sys_token] = (effort, gain);
        d[(loc_limit, ext_token)][sys_token+"+R"] = (effort_random, gain_random);
        rows.append(row);

assert(out_fmt == "tex");
if look_at == 0:
    dump_tex(rows, outf);
else:
    dump_tex2(d, outf);
