#!/usr/bin/env python
from sys import argv, exit
import csv
from os import system
import os

# I finally decide to write this script instead of doing
# more monkey works...
if len(argv) < 3:
    print "monkey.py nameref.csv directory";
    exit(1);

rows = [];
with open(argv[1], "rU") as csvfile:
    creader = csv.reader(csvfile);
    for row in creader:
        rows.append(row);

for root, dirs, files in os.walk(argv[2]):
    for fname in files:
        idx = fname.find(".tar.gz");
        assert( idx != -1);
        key_token = fname[0: idx];
        found = False;
        for row in rows:
            if row[2].find(key_token) != -1:
                found = True;
                app = row[0];
                did = row[1];
                break;
        if found:
            system("mv " + root + "/" + fname + " " + root + "/" + app + "-" + did + ".tar.gz");
