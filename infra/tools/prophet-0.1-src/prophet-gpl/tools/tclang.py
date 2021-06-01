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
from os import environ, path
import subprocess

#FIXME: this is very hacky, should properly handle the quote case
def fix_argv(s):
    if (s[0:2] == "-D") and (s.find('="') != -1):
        idx2 = s.find('="');
        idx3 = s.find('"', idx2 + 2);
        return s[0:idx2] + '=\'"' + s[idx2 + 2: idx3] + '"\'' + s[idx3 + 1:];
    elif (s.find('(') != -1) or (s.find(')') != -1):
        return '"' + s + '"';
    else:
        return s;

for i in range(1, len(argv)):
    argv[i] = fix_argv(argv[i]);

compile_cmd = environ.get("COMPILE_CMD");
assert(compile_cmd != None);
fulldir = path.abspath(path.dirname(argv[0]));
runtime_library_path = fulldir + "/../src/.libs"

just_compile = False;
for i in range(1, len(argv)):
    if argv[i] == "-c":
        just_compile = True;

# This is a link command, I am going to link the library
if not just_compile:
    if (len(argv) > 1 and argv[1].find("-print-prog-name") != 0):
        cmd = compile_cmd + " -Wl,-rpath=" + runtime_library_path + " -L " + runtime_library_path + " " + " ".join(argv[1:]) + " -ltest_runtime";
    else:
        cmd = compile_cmd + " " + " ".join(argv[1:]);
    # print "Linkcmd: " + cmd;
    ret = subprocess.call(cmd, shell=True);
    exit(ret);

cmd = compile_cmd + " " + " ".join(argv[1:]);
ret = subprocess.call(cmd, shell=True);
exit(ret);
