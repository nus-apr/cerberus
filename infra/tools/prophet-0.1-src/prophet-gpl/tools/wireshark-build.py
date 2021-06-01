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
from sys import argv
from os import path, chdir, getcwd, environ, walk
from tester_common import extract_arguments
import subprocess
import getopt

def fix_makefile(makef):
    f = open(makef, "r");
    lines = f.readlines();
    f.close();
    f = open(makef, "w");
    for line in lines:
        tokens = line.strip().split();
        if (len(tokens) > 2) and (tokens[0][0:3] == "AM_") and (tokens[1] == "=") and (tokens[2] == "-Werror"):
            f.write("AM_CFLAGS =\n");
        else:
            f.write(line);
    f.close();

def fix_makefiles(directory):
    for root, dirs, files in walk(directory):
        for fname in files:
            if fname == "Makefile.am":
                fix_makefile(path.join(root, fname));

def fix_pod(podf):
    f = open(podf, "r");
    lines = f.readlines();
    f.close();
    f = open(podf, "w");
    for line in lines:
        if (line.find("peter.kovar") == -1):
            f.write(line);
    f.close();

def fix_epan_makefile(epanf):
    f = open(epanf, "r");
    lines = f.readlines();
    f.close();
    for line in lines:
        if (line.find("noinst_PROGRAMS") != -1) and (line.find("reassemble_test") != -1):
            return;
    f = open(epanf, "w");
    done = False;
    for line in lines:
        if not done:
            if (line.find("reassemble_test:") == 0):
                f.write("noinst_PROGRAMS = reassemble_test tvbtest exntest\n");
                f.write("\n");
                done = True;
        f.write(line);
    f.close();

def fix_top_makefile(topm):
    f = open(topm, "r");
    lines = f.readlines();
    f.close();
    last_line_check = False;
    f = open(topm, "w");
    for line in lines:
        if (line.find("services:") == 0) and (not last_line_check):
            last_line_check = True;
            f.write("services:\n");
        elif (last_line_check):
            last_line_check = False;
            f.write("\ttouch services\n");
        else:
            f.write(line);
    f.close();

def compileit(out_dir, compile_only = False, config_only = False, paraj = 0):
    ori_dir = getcwd();

    my_env = environ;

    chdir(out_dir);
    if not compile_only:
        fix_makefiles(".");
        if (path.exists("epan/Makefile.am")):
            fix_epan_makefile("epan/Makefile.am");
        if (path.exists("Makefile.am")):
            fix_top_makefile("Makefile.am");
        ret = subprocess.call(["./autogen.sh"], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run autogen.sh!";
            chdir(ori_dir);
            exit(1);
        ret = subprocess.call(["./configure --disable-fast-install"], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run configure!";
            chdir(ori_dir);
            exit(1);
        subprocess.call(["make", "clean"], env = my_env);

    if not config_only:
        if paraj == 0:
            subprocess.call(["make"], env = my_env);
        else:
            subprocess.call(["make", "-j", str(paraj)], env = my_env);
        if (path.exists("doc/wireshark.pod")):
            fix_pod("doc/wireshark.pod");
        ret = subprocess.call(["make"], env = my_env);
        if ret != 0:
            print "Failed to make!";
            chdir(ori_dir);
            exit(1);

    chdir(ori_dir);

if __name__ == "__main__":
    deps_dir = getcwd() + "/wireshark-deps"

    compile_only = False;

    opts, args = getopt.getopt(argv[1:],'cd:hj:lp:r:x');
    dryrun_src = "";

    print_fix_log = False;
    print_usage = False;
    config_only = False;
    paraj = 0;
    for o, a in opts:
        if o == "-d":
            dryrun_src = a;
        elif o == "-j":
            paraj = int(a);
        elif o == "-p":
            if a[0] == "/":
                deps_dir = a;
            else:
                deps_dir = getcwd() + "/" + a;
        elif o == "-x":
            config_only = True;
        elif o == "-c":
            compile_only = True;
        elif o == "-l":
            print_fix_log = True;
        elif o == "-h":
            print_usage = True;

    if (len(args) < 1) or (print_usage):
        print "Usage: wireshark-build.py <directory> [-d src_file | -l] [-h]";
        exit(0);

    out_dir = args[0];
    if (path.exists(out_dir)):
        print "Working with existing directory: " + out_dir;
    else:
        print "Non-exist directory";
        exit(1);

    compileit(out_dir, compile_only, config_only, paraj);
    if dryrun_src != "":
        (builddir, buildargs) = extract_arguments(out_dir, dryrun_src);
        if len(args) > 1:
            out_file = open(args[1], "w");
            print >> out_file, builddir;
            print >> out_file, buildargs;
            out_file.close();
        else:
            print builddir;
            print buildargs;
