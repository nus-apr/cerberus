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

for filename in argv[1:]:
    print "Processing: ", filename;
    f = open(filename, "r");
    lines = f.readlines();
    tokens1 = lines[4].strip().split();
    f.close();
    tot = int(tokens1[len(tokens1) - 1]);
    tokens2 = lines[5].strip().split();
    new_tokens = [];
    for token in tokens2:
        if (token == "9436") or (token == "11646") or (token == "10854") \
            or (token == "10916") or (token == "11345") or (token == "11368") \
            or (token == "11659") or (token == "11844") or (token == "1819") or (token == "9408"):
            tot = tot - 1;
            continue;
        new_tokens.append(token);
    f = open(filename, "w");
    f.write(lines[0]);
    f.write(lines[1]);
    f.write(lines[2]);
    f.write(lines[3]);
    f.write(" ".join(tokens1[0:len(tokens1) - 1]) + " " + str(tot) + "\n");
    f.write(" ".join(new_tokens) + "\n");
    f.close();

