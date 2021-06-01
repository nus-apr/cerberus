#!/usr/bin/env python
import os
from sys import argv

res = set();
for root, dirs, files in os.walk(argv[1]):
    for f in files:
        if (f.endswith("-1.c")):
            res.add(int(f[0:len(f) - 4]));

for s in sorted(res):
    print s;
