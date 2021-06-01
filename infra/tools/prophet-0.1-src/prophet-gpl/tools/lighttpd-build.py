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
import subprocess
import getopt

def fix_configure_file(conf_file):
    f = open(conf_file, "r");
    lines = f.readlines();
    f.close();
    f = open(conf_file, "w");
    for line in lines:
        if (line.find("AM_C_PROTOTYPES") != -1):
            continue;
        f.write(line);
    f.close();

# Assume using automake1.11 & installed libpcre3-dev libpcre++-dev libbz2-dev libglib2.0-dev
#
def compile( out_dir, deps_dir, compile_only = False, config_only = False):
    ori_dir = getcwd();
    chdir(out_dir);

    my_env = environ;
    #my_env["PATH"] = deps_dir + "/pcre-8.36-build/bin:" + my_env["PATH"];
    if "PKG_CONFIG_PATH" in my_env:
        my_env["PKG_CONFIG_PATH"] = deps_dir + "/libxml2-2.7.2-build/lib/pkgconfig:"+ my_env["PKG_CONFIG_PATH"];
    else:
        my_env["PKG_CONFIG_PATH"] = deps_dir + "/libxml2-2.7.2-build/lib/pkgconfig";
    my_env["PKG_CONFIG_PATH"] = deps_dir + "/sqlite3-build/lib/pkgconfig:" + my_env["PKG_CONFIG_PATH"];

    # my_env["PATH"] = deps_dir + "/automake-1.11-build/bin:" + my_env["PATH"];

    if not compile_only:
        if (path.exists("configure.ac")):
            fix_configure_file("configure.ac");
        if (path.exists("configure.in")):
            fix_configure_file("configure.in");
        ret = subprocess.call(["sh autogen.sh"], shell=True, env = my_env);
        if ret != 0:
                print "Failed to run autogen.sh, Check automake version!";
                chdir(ori_dir);
                exit(1);
        ret = subprocess.call(["./configure","--disable-fast-install", "--with-ldap", "--with-bzip2", "--with-openssl", "--with-gdbm", "--with-memcache", "--with-webdav-props", "--with-webdav-locks", "--prefix=/home/fanl/Workspace/prophet/build/benchmarks/tmptest/lighttpd-build"], env = my_env);
        if ret != 0:
                print "Configure Error!";
                chdir(ori_dir);
                exit(1);

    if not config_only:
        ret = subprocess.call(["make"], env = my_env);
        if ret != 0:
            print "Failed to compile!";
            exit(1);
    chdir(ori_dir);

    #ret = subprocess.call(["make", "install"], env = my_env);
    #if ret != 0:
#       print "Failed to install! Remember using sudo";
#       exit(1);
#   chdir(ori_dir);

if __name__=="__main__":
    compile_only = False;

    opts, args = getopt.getopt(argv[1:],'cd:hlp:r:x');
    dryrun_src = "";

    print_fix_log = False;
    print_usage = False;
    config_only = False;
    lighttpd_deps_dir = getcwd() + "/lighttpd-deps";

    for o, a in opts:
        if o == "-d":
            dryrun_src = a;
        elif o == "-p":
            if a[0] == "/":
                lighttpd_deps_dir = a;
            else:
                lighttpd_deps_dir = getcwd() + "/" + a;
        elif o == "-x":
            config_only = True;
        elif o == "-c":
            compile_only = True;
        elif o == "-l":
            print_fix_log = True;
        elif o == "-h":
            print_usage = True;

    if (len(args) < 1) or (print_usage):
        print "Usage: lighttpd-build.py <directory> [-d src_file | -l] [-h]";
        exit(0);

    out_dir = args[0];
    # fetch from github if the directory does not exist
    if path.exists(out_dir):
        print "Working with existing directory: " + out_dir;
    else:
        print "Non-exists directory";
        exit(1);

    compile(out_dir, lighttpd_deps_dir, compile_only, config_only);
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

