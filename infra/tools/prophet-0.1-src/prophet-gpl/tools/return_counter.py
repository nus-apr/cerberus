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
f = open("repair.log", "r");
lines = f.readlines();
cnt = 0;
for line in lines:
    tokens = line.strip().split();
    if (len(tokens) > 3):
        if (tokens[0] == "Total") and (tokens[1] == "return"):
            cnt += int(tokens[3]);
        if (tokens[0] == "Total") and (tokens[2] == "different") and (tokens[3] == "repair"):
            cnt += int(tokens[1]);
print "Total size: " + str(cnt);
