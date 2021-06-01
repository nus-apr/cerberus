#!/usr/bin/env python
from os import system, path
from sys import argv, stdout
from getopt import getopt

def invoke_differ(rev, rev_dir):
    src1 = rev_dir + "/" + rev + "-1.c";
    argf1 = rev_dir + "/" + rev + "-1.argf";
    src2 = rev_dir + "/" + rev + "-2.c";
    argf2 = rev_dir + "/" + rev + "-2.argf";
    cmd = differ_cmd + " . " + src1 + " . " + src2 + " -argf " + argf1 + " -argf2 " + argf2 + " -ignore-build-dir ";
    stdout.flush();
    ret = system(cmd);
    return ret == 0;

if __name__ == "__main__":
    fulldir = path.abspath(path.dirname(argv[0]));
    differ_cmd = fulldir + "/../build/src/pdiffer";

    (opt, args) = getopt(argv[1:], "", ["sid=", "eid="]);
    rev_file = args[0];
    rev_dir = args[1];
    out_rev_file = args[2];
    sid = 0;
    eid = 1000000;
    for o, a in opt:
        if o == "--sid":
            sid = int(a);
        elif o == "--eid":
            eid = int(a);

    f = open(rev_file, 'r');
    lines = f.readlines();
    f.close();
    f = open(out_rev_file, 'w');
    cnt = 0;
    line_cnt = 0;
    for line in lines:
        line_cnt += 1;
        if line_cnt <= sid:
            continue;
        if line_cnt > eid:
            continue;
        rev = line.strip();
        stdout.flush();
        print "Processing: " + rev;
        if (invoke_differ(rev, rev_dir)):
            cnt += 1;
            print >> f, rev;
    f.close();
    stdout.flush();
    print "Total we matched: " + str(cnt);
