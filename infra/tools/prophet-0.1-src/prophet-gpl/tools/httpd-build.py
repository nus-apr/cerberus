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

def compileit(out_dir, compile_only = False, config_only = False, paraj = 0):
    ori_dir = getcwd();
    my_env = environ;
    chdir(out_dir);
    if not compile_only:
        ret = subprocess.call(["./buildconf --with-apr=" + deps_dir +"/apr-src --with-apr-util=" + deps_dir + "/apr-util-src"], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run buildconf!";
            chdir(ori_dir);
            exit(1);
        cmd = "./configure --with-apr=" + deps_dir + "/apr-build --with-apr-util=" + deps_dir + "/apr-util-build";
        ret = subprocess.call([cmd], shell = True, env = my_env);
        if (ret != 0):
            print "Failed to run configure!";
            chdir(ori_dir);
            print "Executed: cmd";
            print cmd;
            exit(1);
        subprocess.call(["make", "clean"], shell = True, env = my_env);

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
    deps_dir = getcwd() + "/apache-deps";

    compile_only = False;
    config_only = False;
    paraj = 0;
    dryrun_src = "";

    opts, args = getopt.getopt(argv[1:], 'cd:j:p:');

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
        elif o == "-c":
            compile_only = True;

    print deps_dir;

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
