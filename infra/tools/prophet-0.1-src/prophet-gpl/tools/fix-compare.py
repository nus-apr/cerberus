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
from sys import argv, exit

def normalize(s):
    idx = s.find("abst_hole");
    if (idx != -1):
        idx1 = s.find("(", idx);
        idx2 = idx1 + 1;
        cnt = 1;
        last_idx = idx2;
        tokens = set();
        while (cnt != 0):
            if s[idx2] == "(":
                cnt = cnt + 1;
            if s[idx2] == ")":
                cnt = cnt - 1;
            if (cnt == 1) and (s[idx2] == ","):
                tokens.add(s[last_idx:idx2].strip());
                last_idx = idx2 + 1;
            idx2 = idx2 + 1;
        if (s[last_idx:idx2-1].strip() != ""):
            tokens.add(s[last_idx:idx2-1].strip());
        return (s[0:idx] + "abst_hole(" + s[idx2:], tokens);
    return (s, set());

def check(lines1, lines2):
    if (len(lines1) < len(lines2)):
        return False;
    for i in range(0, len(lines2)):
        (a, tokena) = normalize(lines1[i].strip());
        (b, tokenb) = normalize(lines2[i].strip());
        if (a != b):
            return False;
        for token in tokenb:
            if not token in tokena:
                return False;
    return True;

if __name__ == "__main__":
    if len(argv) < 3:
        exit(1);
    out_file = argv[1];
    ref_file = argv[2];
    fin = open(ref_file, "r");
    ref_lines = fin.readlines();
    fin.close();
    fin = open(out_file, "r");
    out_lines = fin.readlines();
    fin.close();
    one_case = [];
    for line in out_lines:
        if line[0:5] == "=====":
            if (check(one_case[2:], ref_lines)):
                exit(0);
            one_case = [];
        else:
            one_case.append(line);
    exit(1);
