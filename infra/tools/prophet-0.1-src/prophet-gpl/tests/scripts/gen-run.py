#!/usr/bin/env python
import csv

collect = [];

with open("tmp.csv", "rb") as csvfile:
    csvr = csv.reader(csvfile);
    for row in csvr:
        if len(row) > 1:
            app = row[0].strip();
            rev = row[1].strip();
            if app != "" and rev != "":
                collect.append(app + "-" + rev);

n = len(collect);
r = n / 6;
for i in range(0, 6):
    f = open("run" + str(i) + ".sh", 'w');
    e = (i+1) * r;
    if i == 5:
        e = n;
    print >> f, "#!/bin/bash";
    cnt = 0;
    for j in range(i * r, e):
        print >> f, "../../tests/scripts/reproduce.py --init " + collect[j] + " > log" + str(cnt);
        cnt += 1;
    f.close();
