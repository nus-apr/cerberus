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
from sys import argv

dest_dir = argv[1];
log_file = argv[2];

f = open(dest_dir + "/" + log_file, "w");
cnt = 0;
v = [];
for filename in sorted(argv[3:]):
    cnt = cnt + 1;
    cmd = "cp " + filename + " " + dest_dir + "/" + str(cnt)+".t";
    system(cmd);
    v.append(filename);

print >>f, len(v);
for i in range(0, len(v)):
    print >>f, i+1;
    print >>f, v[i];
f.close();
