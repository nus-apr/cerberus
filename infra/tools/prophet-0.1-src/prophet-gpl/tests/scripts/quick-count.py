#!/usr/bin/env python
import glob
import os
import csv
from sys import argv, exit
from os import system
from os import chdir, getcwd

current_cwd = os.path.abspath(os.path.dirname(argv[0]));
defect_list = [];
with open(current_cwd + "/nameref.csv", "rU") as f:
	reader = csv.reader(f);
	for row in reader:
		defect_list.append(row);

in_dir = argv[1];
res = {};
correct_cases = set(["php-307562-307561", "php-307846-307853", "php-308734-308761", "php-309516-309535", "php-309579-309580", "php-309892-309910", "php-310991-310999", "php-311346-311348", "libtiff-ee2ce5b7-b5691a5a", "gmp-13420-13421", "php-307914-307915", "php-308262-308315", "libtiff-d13be72c-ccadf48a", "gzip-a1d3d4019d-f17cbd13a1", "fbc-5458-5459", "php-309688-309716", "php-310011-310050", "php-309111-309159", "libtiff-5b02179-3dfb33b"]);

for root, dirs, files in os.walk(in_dir):
	for fname in files:
		if (fname.find(".tar.gz") == -1):
			continue;
		oid = "";
		for d in defect_list:
			if d[2].strip() == fname:
				oid = d[0] + "-" + d[1];
				break;
		if oid == "":
			print "cannot find " + fname;
			continue;
		if oid in correct_cases:
			continue;
		system("rm -rf __tmp");
		system("mkdir __tmp");
		system("cp " + root + "/" + fname + " __tmp/");
		system("cd __tmp && tar xvzf " + fname);
		a = glob.glob("__tmp/__candidate*");
		if len(a) != 0:
			res[oid] = (len(a), 0);
		system("rm -rf __tmp");

correct_csv = argv[2];
with open(correct_csv, "rU") as f:
	reader = csv.reader(f);
	first = True;
	for row in reader:
		if first:
			first = False;
			continue;
		if (int(row[9]) != 0):
			res[row[0]] = (int(row[9]), int(row[11]));

print res;
print len(res);
for k in res.keys():
	if k in correct_cases:
		continue;
	print k + ", " + str(res[k][0]) + ", " + str(res[k][1]);

for k in res.keys():
	if not k in correct_cases:
		continue;
	print k + ", " + str(res[k][0]) + ", " + str(res[k][1]);
