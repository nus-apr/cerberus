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
from tester_common import extract_arguments, get_fix_revisions
from php_tester import switch_to
import subprocess
import getopt

if __name__=="__main__":
    github_addr = "https://git.php.net/repository/php-src.git";
    php_deps_dir = getcwd() + "/php-deps"

    compile_only = False;
    config_only = False;

    opts, args = getopt.getopt(argv[1:],'cd:hj:lp:r:x');
    dryrun_src = "";
    revision = "";
    paraj = 0;
    print_fix_log = False;
    print_usage = False;
    for o, a in opts:
        if o == "-d":
            dryrun_src = a;
        elif o == "-c":
            compile_only = True;
        elif o == "-x":
            config_only = True;
        elif o == "-p":
            php_deps_dir = a;
        elif o == "-l":
            print_fix_log = True;
        elif o == "-r":
            revision= a;
        elif o == "-h":
            print_usage = True;
        elif o == "-j":
            paraj = int(a);

    if (len(args) < 1) or (print_usage):
        print "Usage: php-build.py <directory> [-r revision | -d src_file | -l] [-h]";
        exit(1);

    out_dir = args[0];
    # fetch from github if the directory does not exist
    if path.exists(out_dir):
        print "Working with existing directory: " + out_dir;
    else:
        ret = system("git clone "+github_addr+" "+out_dir);
        if ret != 0:
            print "Failed to grab from github, check your network connection and make sure you have git!";
            exit(1);

    if print_fix_log:
        ret = get_fix_revisions(out_dir);
        for fix_r, previous_r, comment in ret:
            print "Fix Revision: " + fix_r;
            print "Previous Revision: " + previous_r;
            print "Comment:";
            print comment;
    else:
        if revision != "":
            succ = switch_to(out_dir, revision, php_deps_dir, paraj);
        else:
            succ = switch_to(out_dir, "", php_deps_dir, compile_only, config_only, paraj);
        if (not succ):
            exit(1);
        if dryrun_src != "":
            (builddir, buildargs) = extract_arguments(out_dir, dryrun_src);
            if len(args) > 1:
                out_file = open(args[1], "w");
                print >> out_file, builddir;
                print >> out_file, buildargs;
                out_file.close();
            else:
                print builddir;
                print buildargs;
