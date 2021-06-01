#!/usr/bin/env python
from os import system, path
from sys import argv, stdout
from getopt import getopt

def find_memset(rev, rev_dir):
    src1 = rev_dir + "/" + rev + "-1.c";
    argf1 = rev_dir + "/" + rev + "-1.argf";
    src2 = rev_dir + "/" + rev + "-2.c";
    argf2 = rev_dir + "/" + rev + "-2.argf";
    cmd = differ_cmd + " . " + src1 + " . " + src2 + " -argf " + argf1 + " -argf2 " + argf2 + " -ignore-build-dir -print-memset-only";
    ret = system(cmd);
    return ret == 0;

if __name__ == "__main__":
    fulldir = path.abspath(path.dirname(argv[0]));
    differ_cmd = fulldir + "/../build/src/pdiffer";

    (opt, args) = getopt(argv[1:], "", );
    app = args[0];
    rev_file = "train/raw-revs/" + app + "-raw-revs.txt";
    rev_dir = "train/raw-src/" + app;

    f = open(rev_file, 'r');
    lines = f.readlines();
    f.close();
    cnt = 0;
    res = [];
    for line in lines:
        rev = line.strip();
        stdout.flush();
        print "Processing: " + rev;
        if (find_memset(rev, rev_dir)):
            res.append(rev);

    for rev in res:
        print rev;
