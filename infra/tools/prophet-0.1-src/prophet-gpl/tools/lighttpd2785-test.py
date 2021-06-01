#!/usr/bin/env python
# Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
# Prophet
# 
# This file is part of Prophet.
# 
# Prophet is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# Prophet is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
from sys import argv
from os import system, path, chdir, getcwd, environ
import subprocess

def num2testcase( case ):
	if case=='1':
		return 'cachable'
	elif case=='2':
		return 'core'
	elif case=='3':
		return 'core-condition'
	elif case=='4':
		return 'core-keepalive'
	elif case=='5':
		return 'core-request'
	elif case=='6':
		return 'core-response'
	elif case=='7':
		return 'core-var-include'
	elif case=='8':
		return 'fastcgi'
	elif case=='9':
		return 'lowercase'
	elif case=='10':
		return 'mod-access'
	elif case=='11':
		return 'mod-auth'
	elif case=='12':
		return 'mod-cgi'
	elif case=='13':
		return 'mod-compress'
	elif case=='14':
		return 'mod-redirect'
	elif case=='15':
		return 'mod-rewrite'
	elif case=='16':
		return 'mod-secdownload'
	elif case=='17':
		return 'mod-setenv'
	elif case=='18':
		return 'mod-ssi'
	elif case=='19':
		return 'mod-userdir'
	elif case=='20':
		return 'request'
	elif case=='21':
		return 'symlink'
	else:
		print "Error on case name"
		return 'SOME';

if __name__ == "__main__":
	if len(argv) < 4:
		print "Usage: php-tester.py <src_dir> <test_dir> <work_dir> [cases]";
		exit(1);
	src_dir = argv[1];
	test_dir = argv[2];
	work_dir = argv[3];

	if len(argv) > 4:
		ids = argv[4:];
		
		#print "IDS"
		#print ids;

		my_env = environ;
		ori_dir = getcwd();
		chdir(src_dir + "/tests/");

		ret = subprocess.call(["sh prepare.sh >/dev/null"], shell=True);
		if ret!=0:
			print "Error on preparing";
		else:
			for i in ids:
				testcase = num2testcase(i);
				#print "Testing "+testcase;

				my_env["RUNTESTS"] = testcase;
				ret = subprocess.call(["perl run-tests.pl 1> __out 2>/dev/null"], shell=True, env = my_env);
				if ret!=0:
					#print "Error on testing "+str(i)+": "+testcase;
					continue;

				with open("__out", "r") as fin:
					outs = fin.readlines();

				resultOk = ("Result: PASS\n" in outs);
			
				if (resultOk):
					print i,
				system("rm -rf __out");

			print;

		ret = subprocess.call(["sh cleanup.sh >/dev/null"], shell=True);
		if ret!=0:
			print "Error on cleanup";

		chdir(ori_dir);

