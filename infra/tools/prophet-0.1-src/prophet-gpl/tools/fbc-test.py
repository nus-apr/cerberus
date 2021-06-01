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
import getopt
from os import chdir, getcwd, system, path, environ
import subprocess

if __name__ == "__main__":
    opts, args = getopt.getopt(argv[1 :], "p:");
    profile_dir = "";
    for o, a in opts:
        if o == "-p":
            profile_dir = a;

    src_dir = args[0];
    test_dir = args[1];
    work_dir = args[2];

    if (len(args) > 3):
        ids = args[3 :];
        cur_dir = src_dir;
        if (profile_dir != ""):
            cur_dir = profile_dir;

        if (not path.exists(cur_dir + "/fbc-src/oldtests")):
            system("mv " + cur_dir + "/fbc-src/tests " + cur_dir + "/fbc-src/oldtests");
            system("cp -rf " + test_dir + " " + cur_dir + "/fbc-src/tests");

        #super hacky, because fbc itself calls *ld*, damn it fbc
        fullpath = path.abspath(path.dirname(argv[0]));
        wrappath = fullpath + "/../build/wrap";
        system("rm -rf " + wrappath + "/gcc");
        system("rm -rf " + wrappath + "/cc");

        ori_dir = getcwd();
        chdir(cur_dir + "/fbc-src/tests");
        my_env = environ;
        my_env["PATH"] = wrappath + ":" + my_env["PATH"];
        for i in ids:
            ret = subprocess.call(["timeout 12s ./fbc-run-tests.pl " + i + " 1>/dev/null 2>/dev/null"], shell = True, env = my_env);
            if (ret == 0):
                print i,
        chdir(ori_dir);
