#!/usr/bin/env python
import csv
from sys import argv
from os import system
import os
import getopt

def normalize(casename):
    tokens = casename.strip().split('-');
    newstr = tokens[0];
    if len(tokens[1]) > 6:
        newstr += '-' + tokens[1][0:6];
    else:
        newstr += '-' + tokens[1];
    if len(tokens[2]) > 6:
        newstr += '-' + tokens[2][0:6];
    else:
        newstr += '-' + tokens[2];
    return "{ \\tiny " + newstr + "}";

def transformCSV(csvfname, texfname):
    print csvfname;
    fout = open(texfname, "w");
    print >>fout, "\\begin{tabular}{|l|c|c|c|c|c|c|c|c|c|c|c|c|}";
    print >>fout, "\\hline";
    print >>fout, "\\multirow{3}{*}{\\bf Defect} & \\multicolumn{2}{|c|}{\\bf Search Space} & \\multicolumn{2}{|c|}{\\bf Evaluated} & \\multicolumn{2}{|c|}{\\bf Plausible} & \\multicolumn{2}{|c|}{\\bf Plausible} & \multirow{3}{*}{\parbox[c]{1.2cm}{\\bf Correct Patches}} & \\multicolumn{2}{|c|}{\\bf Correct} & {\\bf Correct} \\\\";
    print >>fout, " &  \\multicolumn{2}{|c|}{\\bf Templates} & \\multicolumn{2}{|c|}{\\bf Templates} & \\multicolumn{2}{|c|}{\\bf Templates} & \\multicolumn{2}{|c|}{\\bf Patches} &     &  \\multicolumn{2}{|c|}{\\bf Template Rank} & {\\bf Patch Rank} \\\\"
    print >>fout, "\\cline{2-3} \\cline{4-5} \\cline{6-7} \\cline{8-9} \\cline{11-12}";
    print >>fout, "& {\\bf All} & {\\bf Cond.} &  {\\bf All} & {\\bf Cond.} & {\\bf All} & {\\bf Cond.} & {\\bf All} & {\\bf Cond.} &  & {\\bf In Space} & {\\bf In Plausible} & {\\bf in Plausible} \\\\";
    print >>fout, "\\hline";
    with open(csvfname, "rU") as csvf:
        csvreader = csv.reader(csvf);
        first_row = True;
        for csvrow in csvreader:
            if first_row:
                first_row = False;
                continue;
            if csvrow[0].find("php") != -1:
                continue;
            print >> fout, normalize(csvrow[0]) + " &",
            print >> fout, csvrow[2] + " &",
            print >> fout, csvrow[3] + " &",
            print >> fout, csvrow[5] + " &",
            print >> fout, csvrow[6] + " &",
            print >> fout, csvrow[7] + " &",
            print >> fout, csvrow[8] + " &",
            print >> fout, csvrow[9] + " &",
            print >> fout, csvrow[10] + " &",
            print >> fout, csvrow[11] + " &",
            if csvrow[4] == "" or csvrow[4] == "0":
                print >> fout, " - &",
            else:
                print >> fout, csvrow[4] + " &",
            if csvrow[13] == "0":
                print >>fout, " - &",
            else:
                print >> fout, csvrow[13] + " &",
            if csvrow[12] == "0":
                print >>fout, " - \\\\";
            else:
                print >> fout, csvrow[12] + " \\\\";
            print >> fout, "\\hline";
    with open(csvfname, "rU") as csvf:
        csvreader = csv.reader(csvf);
        first_row = True;
        for csvrow in csvreader:
            if first_row:
                first_row = False;
                continue;
            if csvrow[0].find("php") == -1:
                continue;
            print >> fout, normalize(csvrow[0]) + " &",
            print >> fout, csvrow[2] + " &",
            print >> fout, csvrow[3] + " &",
            print >> fout, csvrow[5] + " &",
            print >> fout, csvrow[6] + " &",
            print >> fout, csvrow[7] + " &",
            print >> fout, csvrow[8] + " &",
            print >> fout, csvrow[9] + " &",
            print >> fout, csvrow[10] + " &",
            print >> fout, csvrow[11] + " &",
            if csvrow[4] == "" or csvrow[4] == "0":
                print >> fout, " - &",
            else:
                print >> fout, csvrow[4] + " &",
            if csvrow[13] == "0":
                print >>fout, " - &",
            else:
                print >> fout, csvrow[13] + " &",
            if csvrow[12] == "0":
                print >>fout, " - \\\\";
            else:
                print >> fout, csvrow[12] + " \\\\";
            print >> fout, "\\hline";
    print >> fout, "\\end{tabular}";
    fout.close();



(opts, args) = getopt.getopt(argv[1:], "", []);
in_dir = args[0];
out_dir = args[1];

if not os.path.exists(out_dir):
    system("mkdir " + out_dir);

for root, dirs, files in os.walk(in_dir):
    for csvfname in files:
        if (csvfname[len(csvfname) - 4:] != ".csv"):
            continue;
        dot_idx = csvfname.rfind(".");
        if (dot_idx) == -1:
            continue;
        texname = out_dir + "/" + csvfname[0:len(csvfname) -4] + ".tex";
        transformCSV(root + "/" + csvfname, texname);
