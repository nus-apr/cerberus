#!/usr/bin/env python
import getopt
from sys import argv
from os import system

(opts, args) = getopt.getopt(argv[1:], "i:o:",  ["tmp=", "no-mod", "no-sema", "ssvm"]);
in_dir = "train";
out_prefix = "para";
tmp_dir = "__tmp";
no_sema = False;
no_mod = False;
ssvm = False;

for (o, a) in opts:
    if (o == "-i"):
        in_dir = a;
    elif (o == "-o"):
        out_prefix = a;
    elif (o == "--tmp"):
        tmp_dir = a;
    elif (o == "--no-mod"):
        no_mod = True;
    elif (o == "--no-sema"):
        no_sema = True;
    elif (o == "--ssvm"):
        ssvm = True;

extract_cmd = "./extract-feature.py";
if (no_sema):
    extract_cmd += " --disable-sema-cross --disable-sema-value";
    out_prefix += "-no-sema";
if (no_mod):
    extract_cmd += " --disable-mod";
    out_prefix += "-no-mod";
system("rm -rf " + tmp_dir);
system(extract_cmd + " -i " + in_dir + " -o " + tmp_dir + " libtiff apr python php httpd curl wireshark subversion");

tmp_list_prefix = "flist";
app_tokens = ["all", "php", "libtiff", "python", "wireshark"];
#for app in app_tokens:
#    if app != "all":
#        system("./learner-helper.py " + tmp_dir + " " + tmp_list_prefix + "-" + app + ".txt " + app);
#    else:
#        system("./learner-helper.py " + tmp_dir + " " + tmp_list_prefix + "-all.txt");

if (ssvm):
    out_prefix += "-ssvm";

for app in app_tokens:
    learner_cmd = "../build/src/learner";
    if (ssvm):
        learner_cmd += " --algo ssvm";
    system(learner_cmd + " " + tmp_list_prefix + "-" + app + ".txt" + " -o " + out_prefix + "-" + app + ".out");

#for app in app_tokens:
#    system("rm " + tmp_list_prefix + "-" + app + ".txt");

# system("rm -rf " + tmp_dir);
