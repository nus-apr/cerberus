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
import subprocess
from os import system

if __name__ == "__main__":
    f = open("__tmp.c", "w");
    print >> f, "#include <stddef.h>"
    print >> f, "int main() { return 0; }"
    f.close();
    p = subprocess.Popen(["clang", "-v", "__tmp.c", "-o", "__tmp"], stderr = subprocess.PIPE);
    (out, err) = p.communicate();
    lines = err.strip().split("\n");
    enabled = False;
    print "\"",
    for line in lines:
        line = line.strip();
        tokens = line.split();
        if len(tokens) == 0:
            continue;
        if tokens[0] == "#include":
            enabled = True;
        elif tokens[0] == "End":
            enabled = False;
        elif (line[0] == '/') and enabled:
            print "-I"+line+" ",
    print "\""
    system("rm -rf __tmp*");
