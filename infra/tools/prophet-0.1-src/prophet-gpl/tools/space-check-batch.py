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
from os import system
import os
import getopt
from sys import argv

(opts, args) = getopt.getopt(argv[1:], "p:");
prefix = "";
for o, a in opts:
    if o == "-p":
        prefix = a;
assert( len(args) > 2);
in_dir = args[0];
out_dir = args[1];
out_prefix = args[2];

if (not os.path.exists(out_dir)):
    system("mkdir " + out_dir);
for root, dirs, files in os.walk(in_dir):
    for the_dir in dirs:
        if (the_dir[0:len(prefix)] != prefix):
            continue;
        tokens = the_dir.strip().split("-");
        sys = "";
        replace_ext = "";
        cond_ext = "";
        nloc = 200;
        for token in tokens:
            if token == "spr":
                sys = "--spr";
            elif token == "prophet":
                sys = "";
            elif token == "random":
                sys = "--random";
            elif token == "cext":
                cond_ext = "--cond-ext";
            elif token == "rext":
                replace_ext = "--replace-ext";
            else:
                nloc = int(token);

        cmd = "./space-check.py " + sys + " " + replace_ext;
        cmd += " " + cond_ext;
        cmd += " --nloc=" + str(nloc);
        cmd += " " + root+"/"+the_dir;
        cmd += " > " + out_dir + "/" + out_prefix + "-" + the_dir + ".out" + " 2>&1";
        print "Invoke: " + cmd;
        system(cmd);

