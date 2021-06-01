#!/usr/bin/env python
from os import system
import os
from sys import argv
import glob

def handle_out_log(fname):
    f = open(fname, "r");
    should_track = False;
    track_passed_token = False;
    candidate_pass_cnt = 0;
    for line in f:
        tokens = line.strip().split();
        if should_track:
            if track_passed_token:
                if len(tokens) == 1 and tokens[0] == "Passed!":
                    candidate_pass_cnt += 1;
            else:
                if len(tokens) == 3:
                    if tokens[0] == "Passed" and tokens[1] == "Positive" and tokens[2] == "Cases":
                        candidate_pass_cnt += 1;

        if len(tokens) > 1:
            if tokens[0] == "BasicTester,":
                should_track = True;
                track_passed_token = False;
            if tokens[0] == "CondTester,":
                if line.find("Postprocessing") != -1:
                    should_track = True;
                    track_passed_token = True;
                else:
                    should_track = False;
                    track_passed_token = False;
            if tokens[0] == "StringConstTester":
                if line.find("postprocessing!") != -1:
                    should_track = True;
                    track_passed_token = False;
                else:
                    should_track = False;
                    track_passed_token = False;
            if tokens[0] == "StringConstTester,":
                should_track = False;
                track_passed_token = False;
    f.close();
    return candidate_pass_cnt;

assert( len(argv) > 2);
in_dir = argv[1];
out_dir = argv[2];

bad = [];
system("mkdir " + out_dir);
for root, dirs, files in os.walk(in_dir):
    for fname in files:
        if fname[len(fname) - 6:] != "tar.gz":
            continue;
        print "Processing " + fname + ":";
        system("rm -rf __tmp");
        system("mkdir __tmp");
        system("cp " + root + "/" + fname + " __tmp/ball.tar.gz");
        system("cd __tmp && tar xzf ball.tar.gz");

        if not os.path.exists("__tmp/out.log"):
            bad.append(fname);
            system("rm -rf __tmp");
            continue;
        candidate_cnt = handle_out_log("__tmp/out.log");
        system("cd __tmp && tar xzf candidates.tar.gz ");
        candidate_list = glob.glob("__tmp/__candidate*");
        for candidate_fname in candidate_list:
            idx = candidate_fname.find("-");
            the_id = int(candidate_fname[idx+1: len(candidate_fname) - 4]);
            if the_id >= candidate_cnt:
                system("rm " + candidate_fname);
        system("rm __tmp/candidates.tar.gz");
        system("cd __tmp && tar czf candidates.tar.gz __candidate*.txt");
        system("cd __tmp && tar czf newball.tar.gz candidates.tar.gz out.log *fix*.c*");
        system("cp __tmp/newball.tar.gz " + out_dir + "/" +fname);
        system("rm -rf __tmp");

print "Bad tarball:";
for fname in bad:
    print fname;

