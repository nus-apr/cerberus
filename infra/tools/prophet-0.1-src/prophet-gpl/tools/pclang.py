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
from os import system, environ, path
import random
import subprocess

def preprocessGen(src_file, out_file, args, idx):
    new_args = list(args);
    new_args[idx] = src_file;
    has_dash_c = False;
    has_dash_o = False;
    for i in range(0, len(new_args)):
        if (new_args[i] == "-c"):
            has_dash_c = True;
            new_args[i] = "-E";
        if (new_args[i] == "-o"):
            has_dash_o = True;
            if (i == len(new_args) -1):
                print "argument error, -o without filename";
                exit(1);
            new_args[i+1] = out_file;
    if (not has_dash_c):
        new_args.append("-E");
    if (not has_dash_o):
        new_args.append("-o");
        new_args.append(out_file);

    cmd = clang_cmd + " " + " ".join(new_args[1:]);
    print "Invoking: " + cmd;
    ret = subprocess.call(cmd, shell=True);
    return ret;

def rewriteSourceGen(src_file, out_file, args, idx):
    new_args = list(args);
    new_args[idx] = src_file;
    has_dash_c = False;
    for arg in new_args:
        if (arg == "-c"):
            has_dash_c = True;
    if (not has_dash_c):
        new_args.append("-c");
    cmd = clang_cmd + " -Xclang -load -Xclang " + profile_plugin_path + " -Xclang -plugin -Xclang err-profiler-gen " + \
        "-Xclang -plugin-arg-err-profiler-gen -Xclang " + out_file + \
        " -Xclang -plugin-arg-err-profiler-gen -Xclang " + index_file + " " + " ".join(new_args[1:]);
    print "Invoking: " + cmd;
    ret = subprocess.call(cmd, shell=True);
    return ret;

def rewriteSource(src_file, out_file, text_file, args, idx):
    new_args = list(args);
    new_args[idx] = src_file;
    cmd = clang_cmd + " -Xclang -load -Xclang " + profile_plugin_path + " -Xclang -plugin -Xclang err-profiler-rewrite " + \
        " -Xclang -plugin-arg-err-profiler-rewrite -Xclang " + text_file + \
        " -Xclang -plugin-arg-err-profiler-rewrite -Xclang " + out_file + " " + " ".join(new_args[1:]);
    print "Invoking: " + cmd;
    ret = subprocess.call(cmd, shell=True);
    return ret;

def fix_nonnull(src_file, out_file):
    f = open(src_file, "r");
    lines = f.readlines();
    f.close();
    f = open(out_file, "w");
    for line in lines:
        new_line = line;
        idx = line.find("__attribute__((nonnull(");
        if (idx != -1):
            idx2 = line.find(")", idx);
            stem = line[idx+23: idx2];
            tokens = stem.split(",");
            new_t = [];
            for token in tokens:
                x = int(token);
                new_t.append(str(x + 1));
            new_line = line[0:idx] + "__attribute__((nonnull(" + ",".join(new_t) + line[idx2:];
        f.write(new_line);
    f.close();

def finalCompile(src_file, args, idx):
    new_args = list(args);
    new_args[idx] = src_file;
    cmd = clang_cmd + " " + runtime_include_arg + " " + " ".join(new_args[1:]);
    ret = subprocess.call(cmd, shell = True);
    print "invoking: " + cmd;
    return ret;

def cleanup_error(ret):
    system("rm -rf " + tmpfile1);
    system("rm -rf " + tmpfile2);
    system("rm -rf " + tmpfile3);
    exit(ret);

def genTmpFilename():
    cond = True;
    while cond:
        ret = "/tmp/pclang_";
        for i in range(0, 8):
            ret = ret + str(random.randint(0, 9));
        if src_type != "cpp":
            ret = ret + ".c";
        else:
            ret = ret + ".cpp";
        cond = path.exists(ret);
    return ret;

#FIXME: this is very hacky, should properly handle the quote case
def fix_argv(s):
    if (s[0:2] == "-D") and (s.find('="') != -1):
        idx2 = s.find('="');
        idx3 = s.find('"', idx2 + 2);
        return s[0:idx2] + '=\'"' + s[idx2 + 2: idx3] + '"\'' + s[idx3 + 1:];
    elif (s.find('(') != -1) or (s.find(')') != -1):
        return '"' + s + '"';
    else:
        return s;

#new_argv = [];
#i = 0;
#while ( i < len(argv)):
#    if (argv[i][0:2] == "-M"):
#        i = i + 1;
#        if (argv[i][0:3] == "-MQ" or argv[i][0:3] == "-MT" or argv[i][0:3] == "-MF"):
#            i = i + 1;
#        continue;
#    new_argv.append(argv[i]);
#    i = i + 1;

#argv = new_argv;

for i in range(1, len(argv)):
    argv[i] = fix_argv(argv[i]);

clang_cmd = environ.get("COMPILE_CMD");
assert(clang_cmd != None);
index_file = environ.get("INDEX_FILE");
assert(index_file != None);

# print "Invoking pclang here!\n";

fulldir = path.abspath(path.dirname(argv[0]));

profile_plugin_path = fulldir + "/../src/.libs/libprofiler.so.0";
runtime_include_arg = "-I" + fulldir + "/../include";
runtime_library_path = fulldir + "/../src/.libs"
dashed = False;
src_file = "";
src_type = "c";
src_idx = -1;

print argv;
just_compile = False;
found_output = False;
for i in range(1, len(argv)):
    if argv[i] == "-o":
        found_output = True;
    if argv[i] == "-c":
        just_compile = True;
    if argv[i][0] != "-":
        arg = argv[i];
        idx = arg.rfind('.');
        if idx != -1:
            ext = arg[idx+1:];
            if (ext == "c" or ext == "cpp"):
                src_file = argv[i];
                if (ext == "cpp"):
                    src_type = "cpp";
                src_idx = i;

# This is a link command, I am going to link the library
if not just_compile:
    if (len(argv) > 1 and argv[1].find("-print-prog-name") != 0):
        cmd = clang_cmd + " -Wl,-rpath=" + runtime_library_path + " -L " + runtime_library_path + " " + " ".join(argv[1:]) + " -lprofile_runtime";
    else:
        cmd = clang_cmd + " " + " ".join(argv[1:]);
    #print "Non-compile cmd: " + cmd;
    ret = subprocess.call(cmd, shell=True);
    exit(ret);

if (src_idx == -1):
    print "Cannot identify the c source, call original GCC"
    cmd = "/usr/bin/gcc " + " ".join(argv[1:]);
    ret = subprocess.call(cmd, shell=True);
    exit(ret);

if found_output == False:
    argv.append("-o");
    srcfile = argv[src_idx];
    idx = srcfile.rfind(".");
    argv.append(srcfile[0:idx] + ".o");

tmpfile1 = genTmpFilename();
tmpfile2 = genTmpFilename();
tmpfile3 = genTmpFilename();
preprocessGen(src_file, tmpfile1, argv, src_idx);
ret = rewriteSourceGen(src_file, tmpfile2, argv, src_idx);
if (ret != 0):
    cleanup_error(ret);
ret = rewriteSource(tmpfile1, tmpfile3 , tmpfile2, argv, src_idx);
if (ret != 0):
    cleanup_error(ret);
ret = finalCompile(tmpfile3, argv, src_idx);
cleanup_error(ret);
