#!/usr/bin/env python
import os
from sys import argv

assert( len(argv) > 2);
l = [];
if (len(argv) > 3):
    disable_app = argv[3];
else:
    disable_app = "";
order = ["libtiff", "apr", "python", "php", "httpd", "curl", "wireshark", "subversion"];
for root, dirs, files in os.walk(argv[1]):
    for f in files:
        if (disable_app != ""):
            if (root.find(disable_app) != -1):
                continue;
        if (f.endswith(".fvec")):
            l.append(root + "/" + f);

fout = open(argv[2], "w");
for a in order:
    for f in l:
        if f.find(a) != -1:
            print >> fout, f;
fout.close();
