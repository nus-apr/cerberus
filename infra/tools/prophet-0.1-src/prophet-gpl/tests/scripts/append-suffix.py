#!/usr/bin/env python
from os import system
from sys import argv
import csv
import os

mine_to_public = {};
current_cwd = os.path.abspath(os.path.dirname(argv[0]));
with open(current_cwd + "/nameref.csv", "rU") as fin:
    reader = csv.reader(fin);
    for row in reader:
        did = row[0] + "-" + row[1];
        mine_id = row[2][0:len(row[2]) - 7];
        if mine_id != "":
            mine_to_public[mine_id] = did;

the_dir = argv[1];
suffix = argv[2];

for root, dirs, files in os.walk(the_dir):
	for fname in files:
		idx = fname.find('.tar.gz');
		if idx == -1:
			continue;
		mine_id = fname[0:idx];
		if mine_id in mine_to_public:
			new_fname = mine_to_public[mine_id] + "-" + suffix + ".tar.gz";
		system("mv " + root + "/" + fname + " " + root + "/" + new_fname);
