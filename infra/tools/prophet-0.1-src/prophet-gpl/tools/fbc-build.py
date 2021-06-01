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
from os import path, chdir, getcwd, environ
from tester_common import extract_arguments
import subprocess
import getopt

def fix_source(sour):
    f = open(sour, "r");
    lines = f.readlines();
    f.close();
    f = open(sour, "w");
    for line in lines:
        f.write(line);
        if line.find("ldcline += fbc.extopt.ld") != -1:
            f.write('\tldcline += " -l c "\n');
    f.close();

def compileit(out_dir, compile_only = False, config_only = False):
    ori_dir = getcwd();
    chdir(out_dir);

    my_env = environ;

    if not compile_only:
	if (path.exists("fbc-src/src/compiler/fbc_linux.bas")):
            fix_source("fbc-src/src/compiler/fbc_linux.bas");
        ret = subprocess.call(["./configure"], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run configure!";
            chdir(ori_dir);
            exit(1);

    if not config_only:
        ret = subprocess.call(["make"], env = my_env);
        if ret != 0:
            print "Failed to make!";
            chdir(ori_dir);
            exit(1);

    chdir(ori_dir);

if __name__ == "__main__":
    deps_dir = getcwd() + "/fbc-deps"

    compile_only = False;

    opts, args = getopt.getopt(argv[1:],'cd:hlp:r:x');
    dryrun_src = "";

    print_fix_log = False;
    print_usage = False;
    config_only = False;
    for o, a in opts:
        if o == "-d":
            dryrun_src = a;
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
        print "Usage: fbc-build.py <directory> [-d src_file | -l] [-h]";
        exit(0);

    out_dir = args[0];
    if (path.exists(out_dir)):
        print "Working with existing directory: " + out_dir;
    else:
        print "Non-exist directory";
        exit(1);

    compileit(out_dir, compile_only, config_only);
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
