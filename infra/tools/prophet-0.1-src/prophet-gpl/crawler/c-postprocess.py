#!/usr/bin/env python
import os
from sys import argv

def removeAllEmptyLine(fname):
    f = open(fname, "r");
    lines = f.readlines();
    f.close();
    f = open(fname, "w");
    for line in lines:
        strip_line = line.strip();
        if (len(strip_line) != 0):
            f.write(line);
    f.close();

if __name__ == "__main__":
    cdir = argv[1];
    for root, dirs, files in os.walk(cdir):
        for fname in files:
            if fname.endswith(".c"):
                print "Processing: " + fname;
                removeAllEmptyLine(root + "/" + fname);
