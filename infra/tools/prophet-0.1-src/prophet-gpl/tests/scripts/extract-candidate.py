#!/usr/bin/env python
import csv
from os import system
import os
from sys import argv
import glob

def smart_diff(f1, f2):
    fin = open(f1, "r");
    lines1 = fin.readlines();
    fin.close();
    fin = open(f2, "r");
    lines2 = fin.readlines();
    fin.close();
    for idx in range(0, len(lines1)):
        if lines1[idx] == lines2[0]:
            break;
    for i in range(0, len(lines2)):
        if lines1[idx + i] != lines2[i]:
            return False;
    return True;

def check_fix_file(flist, case_id):
    min_id = 10000;
    expfname = current_cmd + "/correct_cexp/" + case_id + ".cexp";
    if not os.path.exists(expfname):
        return min_id;
    expfs = [expfname];
    i = 1;
    while (os.path.exists(expfname + str(i))):
        expfs.append(expfname + str(i));
        i += 1;
    for fname in flist:
        idx = fname.find(".");
        if (idx + 3 > len(fname)):
            fix_id = 0;
        else:
            fix_id = int(fname[idx+3:]);
        for expfname in expfs:
            if smart_diff(fname, expfname):
                if min_id > fix_id:
                    min_id = fix_id;
                    break;
    return min_id + 1;

defect_d = {};
current_cmd = os.path.abspath(os.path.dirname(argv[0]));
with open(current_cmd + "/nameref.csv", "rU") as f:
    reader = csv.reader(f);
    for row in reader:
        defect_d[row[0]+"-"+row[1]] = row[2];

assert( len(argv) > 2);
in_dir = argv[1];
out_dir = argv[2];

system("mkdir " +out_dir);
for root, dirs, files in os.walk(in_dir):
    for fname in files:
        print fname;
        idx = fname.find("-spr-");
        if idx == -1:
            idx = fname.find("-prophet-");
        if idx == -1:
            idx = fname.find("-random-");
        if idx == -1:
            idx = fname.find("-baseline-");
        if (idx == -1):
            continue;
        if len(fname) < 6:
            continue;
        if fname[len(fname) - 6: ] != "tar.gz":
            continue;
        idx2 = fname.find("-fdump");
        if idx2 == -1:
            continue;
        did = fname[0:idx];
        if not did in defect_d:
            continue;
        out_subdir = out_dir + "/" + fname[idx+1:idx2];
        if (not os.path.exists(out_subdir)):
            system("mkdir " + out_subdir);
        system("mkdir __tmp");
        system("cp " + root + "/" + fname + " __tmp/ball.tar.gz");
        system("cd __tmp && tar xvzf ball.tar.gz");

        fix_fn_list = glob.glob("__tmp/*fix*.c*");
        correct_rank = check_fix_file(fix_fn_list, did);
        new_fname = out_dir + "/res-" + fname[0:len(fname) - 6] + "log";
        fout = open(new_fname, "w");
        print >>fout, correct_rank;
        fout.close();

        if (len(glob.glob("__tmp/__candidate*")) != 0) and (not os.path.exists("__tmp/candidates.tar.gz")):
            system("cd __tmp && tar cvzf candidates.tar.gz __candidate*");
        system("cp __tmp/candidates.tar.gz " + out_subdir + "/" + defect_d[did]);
        system("cp __tmp/out.log " + out_dir + "/out-" + did + "-" + fname[idx+1:idx2] + ".log");
        system("rm -rf __tmp");
