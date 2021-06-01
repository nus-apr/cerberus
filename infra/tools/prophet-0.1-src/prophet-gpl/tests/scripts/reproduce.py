#!/usr/bin/env python
import glob
import os
import csv
import getopt
from sys import argv, exit
from os import system
from os import chdir, getcwd

def print_defect():
    print "Available defect/change list:";
    for d in defect_list:
        if d[2].strip() != "":
            print d[0] + '-' + d[1];

(opts, args) = getopt.getopt(argv[1:], "", ["geop=", "nloc=", "bug-file", "parse-space", \
                                            "init", "prophet", "replace-ext", "cond-ext", \
                                            "full-dump", "timeout=", "compare-space", "no-sema", "no-mod", \
                                            "random", "baseline", "ssvm", "dest=", "pass=", "print-fix-only=",
                                            "feature-dump"]);
nof = True;
nloc = 200;
geop = "0.02";
parse_space = False;
init_only = False;
prophet = False;
replace_ext = False;
cond_ext = False;
full_dump = False;
no_sema = False;
no_mod = False;
do_random = False;
loc_only = False;
compare_space = False;
ssvm = False;
dest = "";
password = "";
print_fix_only = "";
timeout = 0;
feature_dump = False;
for o, a in opts:
    if o == "--geop":
        geop = a;
    elif o == "--baseline":
        loc_only = True;
        prophet = True;
    elif o == "--random":
        do_random = True;
    elif o == "--bug-file":
        nof = False;
    elif o == "--nloc":
        nloc = int(a);
    elif o == "--parse-space":
        parse_space = True;
    elif o == "--compare-space":
        compare_space = True;
    elif o == "--no-sema":
        no_sema = True;
    elif o == "--no-mod":
        no_mod = True;
    elif o == "--init":
        init_only = True;
    elif o == "--prophet":
        prophet = True;
    elif o == "--replace-ext":
        replace_ext = True;
    elif o == "--cond-ext":
        cond_ext = True;
    elif o == "--full-dump":
        full_dump = True;
        if timeout == 0:
            timeout = 12;
    elif o == "--timeout":
        timeout = int(a);
    elif o == "--ssvm":
        ssvm = True;
    elif o == "--dest":
        dest = a;
    elif o == "--pass":
        password = a;
    elif o == "--print-fix-only":
        print_fix_only = a;
    elif o == "--feature-dump":
        feature_dump = True;

scenario_addr = "http://rhino.csail.mit.edu/spr-rep/scenarios/";

defect_list = [];
current_cwd = os.path.abspath(os.path.dirname(argv[0]));
with open(current_cwd + "/nameref.csv", "rU") as f:
    reader = csv.reader(f);
    for row in reader:
        defect_list.append(row);

if (len(args) < 1):
    print_defect();
    exit(0);

defect_to_run = args[0];

idx = defect_to_run.find("-");
if (idx == -1):
    print "Invalid defect id";
    print_defect();
    exit(1);

app = defect_to_run[0:idx];
case_id = defect_to_run[idx+1:];
found = False;

for row in defect_list:
    if (app == row[0]) and (case_id == row[1]):
        found = True;
        defect_token = row[2].strip();
        break;

if (not found) or (defect_token == ""):
    print "Unkown defect id";
    print_defect();
    exit(1);

if (not os.path.exists(defect_token)):
    cmd = "wget " + scenario_addr + defect_token;
    ret = system(cmd);
    if (ret != 0):
        print "Downlaod scenario failed, check network status!";
        exit(1);
else:
    print "Work with existing tarball";

cmd = "rm -rf " + app + "-case*";
system(cmd);
cmd = "tar xvzf " + defect_token;
system(cmd);
system("rm -rf *fix*");
glob_res = glob.glob(app + "-case-*");
assert( len(glob_res) > 0);
case_dir = glob_res[0];
glob_res = glob.glob(case_dir + "/" + app + "*workdir");
assert( len(glob_res) > 0);
work_dir = glob_res[0];

if init_only:
    cmd = "rm -rf " + work_dir + "/profile_localization.res";
    system(cmd);
    cmd = "time ../src/prophet -r " + work_dir + " -init-only";
    system(cmd);
elif compare_space:
    ori_dir = getcwd();
    chdir("../../tools");
    cmd = "./space-compare.py";
    if prophet:
        if no_sema:
            cmd += " --no-sema";
        if no_mod:
            cmd += " --no-mod";
        if loc_only:
            cmd += " --loc-only";
        cmd += " --geop=" + geop;
    else:
        cmd += " --spr";
    if do_random:
        cmd += " --random";
    system(cmd);
    chdir(ori_dir);
elif parse_space:
    cmd = "../../tools/spr-correct-compare.py";
    if (not nof):
        cmd += " --bug-file";
    system(cmd);
else:
    cmd = "../src/prophet -r " + work_dir + " -skip-verify";
    if timeout != 0:
        cmd += " -timeout " + str(timeout);
    cmd = "time " + cmd;
    if geop != "0.02":
        cmd += " -geop " + geop;
    if (nof):
        cmd += " -consider-all -first-n-loc " + str(nloc);
    if (do_random):
        cmd += " -random";
    if (loc_only):
        cmd += " -no-feature";
    if (prophet):
        para_file = " ../../crawler/para-";
        if (replace_ext):
            para_file += "rext-";
        if (no_mod):
            para_file += "no-mod-";
        if (no_sema):
            para_file += "no-sema-";
        if (ssvm):
            para_file += "ssvm-";
        if (app == "php") or (app == "libtiff") or (app == "wireshark") or (app == "python"):
            para_file += app +".out";
        else:
            para_file += "all.out";
        cmd += " -feature-para " + para_file;
    if replace_ext:
        cmd += " -replace-ext";
    if cond_ext:
        cmd += " -cond-ext";
    if full_dump:
        cmd += " -full-explore -full-synthesis -dump-passed-candidate __candidate";
    if print_fix_only != "":
        cmd += " -print-fix-only " + print_fix_only;
        if feature_dump:
            cmd += " -dump-feature";
    if dest != "":
        system("rm -rf *fix* out.log repair.log __candidate*");
        cmd += " > out.log";
    print "Invoking: " + cmd;
    system(cmd);
    if dest != "":
        tfile = defect_to_run + "-res.tar.gz";
        if dest[len(dest) - 1] != "/":
            dest += "/";
        if full_dump:
            dest += defect_token;
        else:
            dest += tfile;
        tar_cmd = "tar cvzf " + tfile + " out.log *fix*";
        if full_dump:
            tar_cmd += " __candidate*";
        system(tar_cmd);
        system("sshpass -p '" + password + "' scp " + tfile + " " + dest);
        system("rm -rf " + tfile);
