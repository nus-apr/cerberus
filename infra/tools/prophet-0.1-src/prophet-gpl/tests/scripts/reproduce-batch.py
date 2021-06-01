#!/usr/bin/env python
from os import system
from sys import argv, exit
import getopt

(opts, args) = getopt.getopt(argv[1:], "p:",
                             ["rank-first", "sys=", "nloc=", "rext=", "cext=", "dest=", "full-dump"]);
password = "badpass";
test_sys = ["spr"];
test_locsize = [200];
test_rext = [""];
test_cext = [""];
full_dump = False;
rank_first = False;
dest = "fanl@rhino.csail.mit.edu:/raid/fanl/icse16-result/"
for o, a in opts:
    if o == "-p":
        password = a;
    if o == "--sys":
        if (a == "both"):
            test_sys = ["spr", "prophet"];
        else:
            test_sys = [a];
            assert( (a == "spr") or (a == "prophet"));
    if o == "--nloc":
        toks = a.strip().split(",");
        test_locsize = [];
        for tok in toks:
            test_locsize.append(int(tok));
    if o == "--rext":
        if a == "both":
            test_rext = ["", "--replace-ext"];
        elif a == "on":
            test_rext = ["--replace-ext"];
        else:
            assert(a == "off");
    if o == "--cext":
        if a == "both":
            test_cext = ["", "--cond-ext"];
        elif a == "on":
            test_cext = ["--cond-ext"];
        else:
            assert(a == "off");
    if o == "--dest":
        dest = a;
    if o == "--full-dump":
        full_dump = True;
    if o == "--rank-first":
        rank_first = True;

if (password == "badpass"):
    print "use -p to specify password!";
    exit(1);

for now_case in args:
    for now_sys in test_sys:
        for now_locsize in test_locsize:
            for now_rext in test_rext:
                for now_cext in test_cext:
                    system("rm -rf *fix* __candidate* candidate* out.log repair.log");
                    cmd = "timeout 12h ../../tests/scripts/reproduce.py ";
                    if (now_sys == "prophet"):
                        cmd += "--prophet ";
                        if rank_first:
                            cmd += "--geop 0.99 ";
                    cmd += "--nloc " + str(now_locsize) + " " + now_rext + " " + now_cext;
                    if (full_dump):
                        cmd += " --full-dump";
                    cmd += " " + now_case + " > out.log 2>&1";
                    print "Running: ", cmd;
                    system(cmd);
                    if full_dump:
                        system("tar cvzf candidates.tar.gz __candidate*");
                    tarball = now_case+"-"+now_sys;
                    tarball += "-" + str(now_locsize);
                    if now_sys == "prophet" and rank_first:
                        tarball += "-rfirst";
                    if now_rext != "":
                        tarball += "-rext";
                    if now_cext != "":
                        tarball += "-cext";
                    if full_dump:
                        tarball += "-fdump";
                    tarball +=".tar.gz";
                    print "Create tarball";
                    files = "out.log *fix* ";
                    if full_dump:
                        files += "candidates.tar.gz";
                    system("tar czf " + tarball + " " + files);
                    print "tar czf " + tarball + " " + files;
                    print "Sendback to dest " + dest;
                    system("sshpass -p '" + password + "' scp " + tarball + " " + dest);
                    system("rm -rf " + tarball);
