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

def is_config_line(s):
    return s.find("CONFIGFILE") != -1;

def is_start_proc_line(s):
    return s.find("start_proc") != -1;

def is_stop_proc_line(s):
    return s.find("stop_proc") != -1;

def is_request_line(s):
    return s.find("REQUEST") != -1 and s.find("$t") != -1;

assert(len(argv) == 2);
filename = argv[1];

idx = filename.rfind(".");
filebody = filename[0 : idx];
ext = filename[idx+1 :];

headers = [];
f = open(filename, "r");
lines = f.readlines();
f.close();
res = [];
trails = [];

in_header = True;
in_trail = False;
last_request = [];

for line in lines:
    s = line.strip();

    if (is_request_line(s)):
        in_header = False;
        if (len(last_request) != 0):
            res.append(last_request);
        last_request = [line];
    elif (is_stop_proc_line(s)):
        if (len(last_request) != 0):
            res.append(last_request);
        in_trail = True;
    elif (not in_header) and (not in_trail):
        if ((s != "") and (line[0] != '#')) or (len(last_request) != 0):
            last_request.append(line);

    if (in_header):
        if (line.find("Test::More") == -1):
            headers.append(line);
        else:
            headers.append("use Test::More tests => 5;\n");

    if (in_trail):
        trails.append(line);


for i in range(0, len(res)):
    f = open(filebody + "-" + str(i) + ".t", "w");
    for line in headers:
        f.write(line);
    for line in res[i]:
        f.write(line);
    for line in trails:
        f.write(line);
    f.close();

