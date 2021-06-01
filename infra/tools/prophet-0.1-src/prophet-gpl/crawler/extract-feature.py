#!/usr/bin/env python
import getopt
from sys import argv
from os import system

(opts, args) = getopt.getopt(argv[1:], "i:o:r:", ["disable-sema-cross", "disable-sema-value", "disable-mod", "replace-ext"]);
in_dir = "train";
out_dir = "__tmp";
differ_cmd = "../build/src/pdiffer"
disable_sema_cross = False;
disable_sema_value = False;
disable_mod = False;
replace_ext = False;
for (o, a) in opts:
    if (o == "-i"):
        in_dir = a;
    elif (o == "-o"):
        out_dir = a;
    elif (o == "-r"):
        differ_cmd = a;
    elif (o == "--disable-sema-cross"):
        disable_sema_cross = True;
    elif (o == "--disable-sema-value"):
        disable_sema_value = True;
    elif (o == "--disable-mod"):
        disable_mod = True;
    elif (o == "--replace-ext"):
        replace_ext = True;

if (disable_sema_cross):
    differ_cmd += " -disable-sema-cross";
if (disable_sema_value):
    differ_cmd += " -disable-sema-value";
if (disable_mod):
    differ_cmd += " -disable-mod";
if (replace_ext):
    differ_cmd += " -replace-ext";

system("mkdir " + out_dir);
for app in args:
    print "======================================";
    print "Processing " + app + ":";
    app_dir = out_dir + "/" + app;
    system("mkdir " + app_dir);
    app_rev_f = in_dir + "/inspace-revs/" + app + "-inspace-revs.txt";
    app_src_dir = in_dir + "/raw-src/" + app;
    f = open(app_rev_f, "r");
    lines = f.readlines();
    f.close();
    for line in lines:
        rev = line.strip();
        print "Processing revision " + rev;
        src_1 = app_src_dir + "/" + rev + "-1.c";
        src_2 = app_src_dir + "/" + rev + "-2.c";
        argf_1 = app_src_dir + "/" + rev + "-1.argf";
        argf_2 = app_src_dir + "/" + rev + "-2.argf";
        out_f = app_dir + "/" + rev + ".fvec";
        cmd = differ_cmd + " . " + src_1 + " . " + src_2 + " -argf " + argf_1 + " -argf2 " + argf_2 + " -ignore-build-dir -extract-feature " + out_f;
        print "Executing: " + cmd;
        ret = system(cmd);
        assert( ret == 0);
