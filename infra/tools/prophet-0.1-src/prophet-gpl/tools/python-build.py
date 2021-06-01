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
from os import path, chdir, getcwd, environ, system
from tester_common import extract_arguments
import subprocess
import getopt

def fix_setup_script(setup_script):
    f = open(setup_script, "r");
    lines = f.readlines();
    f.close();
    f = open(setup_script, "w");
    for line in lines:
        if (line.find("lib_dirs") != -1) and (line.find("self.compiler.library_dirs +") != -1) and (line.find("/usr/lib/x86_64-linux-gnu") == -1):
            j = line.rfind("\n");
            f.write(line[:j] + "'/usr/lib/x86_64-linux-gnu',\n");
        else:
            f.write(line);
    f.close();

def fix_asdl_py(asdl_c):
    f = open(asdl_c, "r");
    lines = f.readlines();
    f.close();
    f = open(asdl_c, "w");
    for line in lines:
        if (line.find('self.emit("default:" % name, 2)') != -1):
            j = line.find('self.emit("default:" % name');
            f.write(line[:j] + 'self.emit("default:", 2)\n');
        else:
            f.write(line);
    f.close();


def compileit(out_dir, compile_only = False, config_only = False, paraj = 0):
    ori_dir = getcwd();
    chdir(out_dir);

    my_env = environ;

    if not compile_only:
        system("rm -rf Modules/Setup Modules/config.c Makefile");
        if (path.exists("setup.py")):
            fix_setup_script("setup.py");
        if (path.exists("Parser/asdl_c.py")):
            fix_asdl_py("Parser/asdl_c.py");
        ret = subprocess.call(["./configure"], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run configure!";
            chdir(ori_dir);
            exit(1);
        subprocess.call(["make", "clean"], env = my_env);

    if not config_only:
        if paraj == 0:
            ret = subprocess.call(["make"], env = my_env);
        else:
            ret = subprocess.call(["make", "-j", str(paraj)], env = my_env);
        if ret != 0:
            print "Failed to make!";
            chdir(ori_dir);
            exit(1);

    chdir(ori_dir);

if __name__ == "__main__":
    deps_dir = getcwd() + "/python-deps"

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
        print "Usage: python-build.py <directory> [-d src_file | -l] [-h]";
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
