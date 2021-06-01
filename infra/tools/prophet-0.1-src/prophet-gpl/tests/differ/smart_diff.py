#!/usr/bin/env python

from sys import argv, exit

if (len(argv) != 3):
    exit(1);

f1 = open(argv[1], "r");
lines1 = f1.readlines();
f1.close();
f2 = open(argv[2], "r");
lines2 = f2.readlines();
f2.close();
if (len(lines1) != len(lines2)):
    print "Differnt number of lines!";
    exit(1);

for i in range(0, len(lines1)):
    tokens1 = lines1[i].strip(" ").split(" ");
    tokens2 = lines2[i].strip(" ").split(" ");
    if (len(tokens1) != len(tokens2)):
        print "DIFF at line" + str(i) + " :";
        print lines1[i];
        print "AND"
        print lines2[i];
        exit(1);
    for j in range(0, len(tokens1)):
        if (tokens1[j][0:2] == "0x" and tokens2[j][0:2] == "0x"):
            continue;
        if (tokens1[j] != tokens2[j]):
            print "DIFF at line" + str(i) + " :";
            print lines1[i];
            print "AND"
            print lines2[i];
            exit(1);
