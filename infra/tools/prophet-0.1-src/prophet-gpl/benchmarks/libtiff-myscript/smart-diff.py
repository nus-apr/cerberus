#!/usr/bin/env python
from sys import argv
from os import path

reffile = argv[2];
infile = argv[1];
tol = set();
if (path.exists(reffile)):
    f = open(reffile, "r");
    lines = f.readlines();
    f.close();
    for line in lines:
        tokens = line.strip().split();
        if (len(tokens) < 2):
            continue;
        if tokens[0] == "<" or tokens[0] == ">":
            tol.add(int(tokens[1][0:len(tokens[1]) - 1], 16));

f = open(infile, "r");
lines = f.readlines();
f.close();
for line in lines:
    tokens = line.strip().split();
    if (len(tokens) < 2):
        continue;
    if (tokens[0] == "<" or tokens[0] == ">"):
        v = int(tokens[1][0:len(tokens[1]) - 1], 16);
        if (v == 0):
            continue;
        # non-determinism part of the file, we are going to ignore
        if (v >= 0x5900 and v <= 0x6200):
            continue;
        if (v == 0x2010):
            continue;
        found = False;
        for x in tol:
            if (abs(v - x) < 512):
                found = True;
                break;
        if not found:
            print line
            exit(1);
