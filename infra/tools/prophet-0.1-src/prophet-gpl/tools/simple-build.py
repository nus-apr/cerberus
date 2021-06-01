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
import getopt
from sys import argv
import subprocess
from os import chdir, getcwd, path, environ
from tester_common import extract_arguments

def tobuild(src_dir):
    ori_dir = getcwd();
    print "Path env: ", environ["PATH"];
    chdir(src_dir);
    ret = subprocess.call("make");
    chdir(ori_dir);
    return ret == 0;

if __name__ == "__main__":
    opts, args = getopt.getopt(argv[1:], "cd:hx");
    dryrun_src = "";
    compile_only = False;
    print_usage = False;
    config_only = False;
    for o, a in opts:
        if o == "-x":
            config_only = True;
        if o == "-d":
            dryrun_src = a;
        elif o == "-c":
            compile_only = True;
        elif o == "-h":
            print_usage = True;

    if config_only:
        exit(0);

    if ((len(args) < 1) or (print_usage)):
        print "Usage: simple-build.py <dirctory> [-d src_file | -c] [-h]";
        exit(0);

    out_dir = args[0];
    # fetch from github if the directory does not exist
    if (not path.exists(out_dir)):
        print "Directory does not exist!";
        exit(1);

    if (not tobuild(out_dir)):
        print "Build failed!";
        exit(1);

    if dryrun_src != "":
        build_dir, build_args = extract_arguments(out_dir, dryrun_src);
        if (len(args) > 1):
            out_file = open(args[1], "w");
            print >>out_file, build_dir
            print >>out_file, build_args
            out_file.close();
        else:
            print build_dir;
            print build_args;
