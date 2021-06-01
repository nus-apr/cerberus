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
from sys import argv, exit
import getopt

(opts, args) = getopt.getopt(argv[1:], "p:",
                             ["sys=", "nloc=", "rext=", "cext=", "dest="]);
password = "badpass";
test_sys = ["spr"];
test_locsize = [200];
test_rext = [""];
test_cext = [""];
full_dump = False;
dest = "fanl@rhino.csail.mit.edu:/raid/fanl/icse16-result/"
for o, a in opts:
    if o == "-p":
        password = a;
    if o == "--sys":
        if (a == "both"):
            test_sys = ["spr", "prophet"];
        else:
            test_sys = [a];
            assert( (a == "spr") or (a == "prophet"));
    if o == "--nloc":
        toks = a.strip().split(",");
        test_locsize = [];
        for tok in toks:
            test_locsize.append(int(tok));
    if o == "--rext":
        if a == "both":
            test_rext = ["", "--replace-ext"];
        elif a == "on":
            test_rext = ["--replace-ext"];
        else:
            assert(a == "off");
    if o == "--cext":
        if a == "both":
            test_cext = ["", "--cond-ext"];
        elif a == "on":
            test_cext = ["--cond-ext"];
        else:
            assert(a == "off");
    if o == "--dest":
        dest = a;

if (password == "badpass"):
    print "use -p to specify password!";
    exit(1);

for now_sys in test_sys:
    for now_locsize in test_locsize:
        for now_rext in test_rext:
            for now_cext in test_cext:
                system("rm -rf __tmp*");
                cmd = "./space-compare.py ";
                if (now_sys == "spr"):
                    cmd += "--spr ";
                outlog = "space-" + now_sys + "-" + str(now_locsize);
                if now_rext != "":
                    outlog += "-rext";
                if now_cext != "":
                    outlog += "-cext";
                outlog +=".out";
                cmd += "--nloc " + str(now_locsize) + " " + now_rext + " " + now_cext;
                cmd += " > " + outlog + " 2>&1";
                print "Running: ", cmd;
                system(cmd);
                print "Sendback to dest " + dest;
                system("sshpass -p '" + password + "' scp " + outlog + " " + dest);
                system("rm -rf " + outlog);
