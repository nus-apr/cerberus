#!/usr/bin/env python
from sys import argv, exit
import csv
from os import system
import os

# I finally decide to write this script instead of doing
# more monkey works...
if len(argv) < 4:
    print "monkey.py nameref.csv directory target-dir";
    exit(1);

rows = [];
with open(argv[1], "rU") as csvfile:
    creader = csv.reader(csvfile);
    for row in creader:
        rows.append(row);

system("mkdir " + argv[3]);
for root, dirs, files in os.walk(argv[2]):
    for fname in files:
        idx = fname.find("-fix-");
        assert( idx != -1);
        key_token = fname[idx + 5: idx+9];
        if key_token == "test":
            idx = fname.find("-fix-tests");
            idx = fname.find("-", idx + 9);
            key_token = fname[idx + 1: idx + 5];
        found = False;
        for row in rows:
            if row[2].find(key_token) != -1:
                found = True;
                app = row[0];
                did = row[1];
                break;
        if found:
            system("mkdir " + argv[3] + "/" + app + '-' + did);
            system("cp " + root + "/" + fname + " " + argv[3] + "/" + app + "-" + did + "/");
