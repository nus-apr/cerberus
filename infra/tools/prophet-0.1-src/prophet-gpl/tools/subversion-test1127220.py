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
	if case=="1":
		return "subversion/tests/libsvn_subr/auth-test"
	elif case=="2":
		return "subversion/tests/libsvn_subr/cache-test"
	elif case=="3":
		return "subversion/tests/libsvn_subr/checksum-test"
	elif case=="4":
		return "subversion/tests/libsvn_client/client-test"
	elif case=="5":
		return "subversion/tests/libsvn_subr/compat-test"
	elif case=="6":
		return "subversion/tests/libsvn_subr/config-test"
	elif case=="7":
		return "subversion/tests/libsvn_wc/db-test"
	elif case=="8":
		return "subversion/tests/libsvn_diff/diff-diff3-test"
	elif case=="9":
		return "subversion/tests/libsvn_subr/dirent_uri-test"
	elif case=="10":
		return "subversion/tests/libsvn_wc/entries-compat-test"
	elif case=="11":
		return "subversion/tests/libsvn_subr/eol-test"
	elif case=="12":
		return "subversion/tests/libsvn_subr/error-test"
	elif case=="13":
		return "subversion/tests/libsvn_fs_fs/fs-pack-test"
	elif case=="14":
		return "subversion/tests/libsvn_fs/fs-test"
	elif case=="15":
		return "subversion/tests/libsvn_subr/hashdump-test"
	elif case=="16":
		return "subversion/tests/libsvn_fs/locks-test"
	elif case=="17":
		return "subversion/tests/libsvn_subr/mergeinfo-test"
	elif case=="18":
		return "subversion/tests/libsvn_wc/op-depth-test"
	elif case=="19":
		return "subversion/tests/libsvn_subr/opt-test"
	elif case=="20":
		return "subversion/tests/libsvn_diff/parse-diff-test"
	elif case=="21":
		return "subversion/tests/libsvn_subr/path-test"
	elif case=="22":
		return "subversion/tests/libsvn_wc/pristine-store-test"
	elif case=="23":
		return "subversion/tests/libsvn_ra_local/ra-local-test"
	elif case=="24":
		return "subversion/tests/libsvn_delta/random-test"
	elif case=="25":
		return "subversion/tests/libsvn_repos/repos-test"
	elif case=="26":
		return "subversion/tests/libsvn_subr/revision-test"
	elif case=="27":
		return "subversion/tests/libsvn_subr/skel-test"
	elif case=="28":
		return "subversion/tests/libsvn_subr/stream-test"
	elif case=="29":
		return "subversion/tests/libsvn_subr/string-test"
	elif case=="30":
		return "subversion/tests/libsvn_subr/subst_translate-test"
	elif case=="31":
		return "subversion/tests/libsvn_subr/target-test"
	elif case=="32":
		return "subversion/tests/libsvn_subr/time-test"
	elif case=="33":
		return "subversion/tests/libsvn_subr/translate-test"
	elif case=="34":
		return "subversion/tests/libsvn_wc/tree-conflict-data-test"
	elif case=="35":
		return "subversion/tests/libsvn_subr/utf-test"
	elif case=="36":
		return "subversion/tests/libsvn_delta/window-test"
	elif case=="37":
		return "subversion/tests/cmdline/authz_tests.py"
	elif case=="38":
		return "subversion/tests/cmdline/autoprop_tests.py"
	elif case=="39":
		return "subversion/tests/cmdline/basic_tests.py"
	elif case=="40":
		return "subversion/tests/cmdline/blame_tests.py"
	elif case=="41":
		return "subversion/tests/cmdline/cat_tests.py"
	elif case=="42":
		return "subversion/tests/cmdline/changelist_tests.py"
	elif case=="43":
		return "subversion/tests/cmdline/checkout_tests.py"
	elif case=="44":
		return "subversion/tests/cmdline/commit_tests.py"
	elif case=="45":
		return "subversion/tests/cmdline/copy_tests.py"
	elif case=="46":
		return "subversion/tests/cmdline/depth_tests.py"
	elif case=="47":
		return "subversion/tests/cmdline/diff_tests.py"
	elif case=="48":
		return "subversion/tests/cmdline/entries_tests.py"
	elif case=="49":
		return "subversion/tests/cmdline/export_tests.py"
	elif case=="50":
		return "subversion/tests/cmdline/externals_tests.py"
	elif case=="51":
		return "subversion/tests/cmdline/getopt_tests.py"
	elif case=="52":
		return "subversion/tests/cmdline/history_tests.py"
	elif case=="53":
		return "subversion/tests/cmdline/import_tests.py"
	elif case=="54":
		return "subversion/tests/cmdline/info_tests.py"
	elif case=="55":
		return "subversion/tests/cmdline/input_validation_tests.py"
	elif case=="56":
		return "subversion/tests/cmdline/lock_tests.py"
	elif case=="57":
		return "subversion/tests/cmdline/log_tests.py"
	elif case=="58":
		return "subversion/tests/cmdline/merge_authz_tests.py"
	elif case=="59":
		return "subversion/tests/cmdline/merge_reintegrate_tests.py"
	elif case=="60":
		return "subversion/tests/cmdline/merge_tests.py"
	elif case=="61":
		return "subversion/tests/cmdline/merge_tree_conflict_tests.py"
	elif case=="62":
		return "subversion/tests/cmdline/mergeinfo_tests.py"
	elif case=="63":
		return "subversion/tests/cmdline/patch_tests.py"
	elif case=="64":
		return "subversion/tests/cmdline/prop_tests.py"
	elif case=="65":
		return "subversion/tests/cmdline/redirect_tests.py"
	elif case=="66":
		return "subversion/tests/cmdline/resolve_tests.py"
	elif case=="67":
		return "subversion/tests/cmdline/resolved_tests.py"
	elif case=="68":
		return "subversion/tests/cmdline/revert_tests.py"
	elif case=="69":
		return "subversion/tests/cmdline/schedule_tests.py"
	elif case=="70":
		return "subversion/tests/cmdline/special_tests.py"
	elif case=="71":
		return "subversion/tests/cmdline/stat_tests.py"
	elif case=="72":
		return "subversion/tests/cmdline/svnadmin_tests.py"
	elif case=="73":
		return "subversion/tests/cmdline/svndumpfilter_tests.py"
	elif case=="74":
		return "subversion/tests/cmdline/svnlook_tests.py"
	elif case=="75":
		return "subversion/tests/cmdline/svnrdump_tests.py"
	elif case=="76":
		return "subversion/tests/cmdline/svnsync_tests.py"
	elif case=="77":
		return "subversion/tests/cmdline/svnversion_tests.py"
	elif case=="78":
		return "subversion/tests/cmdline/switch_tests.py"
	elif case=="79":
		return "subversion/tests/cmdline/trans_tests.py"
	elif case=="80":
		return "subversion/tests/cmdline/tree_conflict_tests.py"
	elif case=="81":
		return "subversion/tests/cmdline/update_tests.py"
	elif case=="82":
		return "subversion/tests/cmdline/upgrade_tests.py"
	elif case=="83":
		return "subversion/tests/cmdline/utf8_tests.py"
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

		ori_dir = getcwd();
		chdir(src_dir + "/tests/");

		for i in ids:
			testcase = num2testcase(i);
			#print "Testing "+testcase;

			ret = subprocess.call(["make","check","CLEANUP=true", "TESTS="+testcase,">/dev/null"], shell=True);
			if ret==0:
				print i,

		print;
		chdir(ori_dir);

