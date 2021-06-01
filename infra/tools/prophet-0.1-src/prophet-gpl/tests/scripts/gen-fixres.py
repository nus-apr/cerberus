#!/usr/bin/env python
from sys import argv
from os import system
import os
import getopt
import csv

defect_list = [];
current_cwd = os.path.abspath(os.path.dirname(argv[0]));
with open(current_cwd + "/nameref.csv", "rU") as f:
    reader = csv.reader(f);
    for row in reader:
        defect_list.append(row);

opts, args = getopt.getopt(argv[1:], "", ["prophet", "spr", "fbc-only", "local-only", "feature-dump", "cleanup", "onlydo="]);

prophet = True;
spr = False;
fbc_only = False;
cleanup = False;
feature_dump = False;
local_only = False;
onlydo_start = 0;
onlydo_end = 10000;
for o, a in opts:
    if o == "--prophet":
        prophet = True;
        spr = False;
    elif o == "--spr":
        spr = True;
        prophet = False;
    elif o == "--fbc-only":
        fbc_only = True;
    elif o == "--cleanup":
        cleanup = True;
    elif o == "--feature-dump":
        feature_dump = True;
    elif o == "--local-only":
        local_only = True;
    elif o == "--onlydo":
        tokens = a.split(":");
        onlydo_start = int(tokens[0]);
        onlydo_end = int(tokens[1]);

cnt = 0;
for d in defect_list:
    cmd = current_cwd + "/reproduce.py --print-fix-only " + d[0] + "-" + d[1] + ".fres ";
    tarfile = d[2].strip();
    if tarfile == "":
        continue;
    if (local_only and not os.path.exists(tarfile)):
        continue;
    if fbc_only:
        if d[0].find("fbc") != 0:
            continue;
    else:
        if d[0].find("fbc") == 0:
            continue;
    skip = False;
    if cnt < onlydo_start or cnt >= onlydo_end:
        skip = True;
    cnt += 1;
    if skip:
        continue;
    if prophet:
        cmd += "--prophet ";
    if feature_dump:
        cmd += "--feature-dump ";
    cmd += d[0] + "-" + d[1];
    print cmd;
    system(cmd);
    if cleanup:
        system("rm -rf *.tar.gz");
        system("rm -rf *-case-*/");
