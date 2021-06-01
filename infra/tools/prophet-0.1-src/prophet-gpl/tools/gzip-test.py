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

cases = [
    "helin-segv",
    "hufts",
    "memcpy-abuse",
    "mixed",
    "null-suffix-clobber",
    "stdin",
    "trailing-nul",
    "zdiff",
    "zgrep-f",
    "zgrep-signal",
    "znew-k"];

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

        if (not path.exists(cur_dir + "/mytests")):
            system("cp -rf " + test_dir + " " + cur_dir + "/mytests");

        if (not path.exists(cur_dir + "/build-aux/test-driver")):
			if (path.exists(test_dir + "/test-driver")):
				system("cp -rf " + test_dir + "/test-driver " + cur_dir + "/build-aux/test-driver");

        ori_dir = getcwd();
        chdir(cur_dir + "/mytests");
        my_env = environ;
        for i in ids:
            case_str = cases[int(i) - 1];
            ret = subprocess.call(["./" + case_str + " 1>/dev/null 2>/dev/null"], shell = True);
            if (ret == 0):
                print i,
        chdir(ori_dir);
