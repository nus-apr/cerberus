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
from php_tester import php_tester
from sys import argv
import getopt
from os import system
import os

if __name__ == "__main__":
    if len(argv) < 4:
        print "Usage: php-tester.py <src_dir> <test_dir> <work_dir> [cases]";
        exit(1);

    opts, args = getopt.getopt(argv[1:], "p:");
    profile_dir = "";
    for o, a in opts:
        if o == "-p":
            profile_dir = a;

    src_dir = args[0];
    test_dir = args[1];
    work_dir = args[2];
    if len(args) > 3:
        ids = args[3:];
        a = php_tester(work_dir, src_dir, test_dir);
        s = [];
        for i in ids:
            s.append(int(i));
        ret = a.test(s, profile_dir);
        for i in ret:
            print i,
        print;
        if len(ids) == 1 and len(ret) == 0:
            if "OUTIFFAIL" in os.environ:
                outf = work_dir + "/__cleantests/" + ids[0] + ".out";
                if os.path.exists(outf):
                    system("cp -rf " + outf + " " + os.environ["OUTIFFAIL"]);
            if "EXPIFFAIL" in os.environ:
                expf = work_dir + "/__cleantests/" + ids[0] + ".exp";
                if os.path.exists(expf):
                    system("cp -rf " + expf + " " + os.environ["EXPIFFAIL"]);
