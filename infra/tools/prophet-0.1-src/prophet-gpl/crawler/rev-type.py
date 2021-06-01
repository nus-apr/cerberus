#!/usr/bin/env python
from os import system, path
from sys import argv, stdout
import subprocess
from getopt import getopt

def get_type(rev, rev_dir):
    src1 = rev_dir + "/" + rev + "-1.c";
    argf1 = rev_dir + "/" + rev + "-1.argf";
    src2 = rev_dir + "/" + rev + "-2.c";
    argf2 = rev_dir + "/" + rev + "-2.argf";
    cmd = differ_cmd + " . " + src1 + " . " + src2 + " -argf " + argf1 + " -argf2 " + argf2 + " -ignore-build-dir -print-match-kind";
    p = subprocess.Popen(cmd.split(), stdout = subprocess.PIPE);
    (out, err) = p.communicate();
    lines = out.split("\n");
    ret = -1;
    for line in lines:
        tokens = line.strip().split();
        if (len(tokens) > 1) and (tokens[0] == "CandidateType:"):
            ret = int(tokens[1]);
            break;
    return ret;

if __name__ == "__main__":
    fulldir = path.abspath(path.dirname(argv[0]));
    differ_cmd = fulldir + "/../build/src/pdiffer";

    (opt, args) = getopt(argv[1:], "", );
    app = args[0];
    rev_file = "train/inspace-revs/" + app + "-inspace-revs.txt";
    rev_dir = "train/raw-src/" + app;

    f = open(rev_file, 'r');
    lines = f.readlines();
    f.close();
    cnt = 0;
    d = [0,0,0,0,0,0,0,0];
    for line in lines:
        rev = line.strip();
        stdout.flush();
        print "Processing: " + rev;
        ret = get_type(rev, rev_dir);
        if ret != -1:
            d[ret] += 1;

    for n in d:
        print n;
