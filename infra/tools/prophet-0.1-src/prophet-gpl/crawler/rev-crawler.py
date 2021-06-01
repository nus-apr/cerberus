#!/usr/bin/env python
import getopt
from sys import argv
from os import system, path
import os
from repo_handler import create_repo_handler

build_log = "__build.log";
para = 0;

def generate_arg_file(src_dir, src_file, arg_file, deps_dir, force_rebuilt):
    if not force_rebuilt:
        print "Normal Compiling....";
        cmd = build_cmd;
        if para != 0:
            cmd += " -j " + str(para);
        cmd += " -p " + deps_dir + " -d " + src_file + " -c " + src_dir + " " + arg_file + " >>" + build_log + " 2>&1";
        ret = system(cmd);
    else:
        ret = 1;

    if (ret != 0):
        print "Full Compiling...."
        cmd = build_cmd;
        if para != 0:
            cmd += " -j " + str(para);
        cmd += " -p " + deps_dir + " -d " + src_file +" " + src_dir + " " + arg_file + " >>" + build_log + " 2>&1";
        ret = system(cmd);
        if (ret != 0):
            return False;
    return True;

def parseArgFile(src_dir, arg_file):
    f = open(arg_file, "r");
    lines = f.readlines();
    assert( len(lines) > 1);
    build_dir = lines[0].strip();
    if (build_dir == "."):
        build_dir = src_dir;
    args = lines[1].strip().split();
    i = 0;
    new_args = [];
    disabled_options = set(["-c", "-Wlogical-op", "-fno-delete-null-pointer-checks", "-fno-strict-overflow", "-fno-strict-overflow", "-Wlogical-op", "-Wjump-misses-init", "-prefer-non-pic", "-prefer-pic"]);
    while (i < len(args)):
        if (args[i] == "-o"):
            i+=1;
        elif not (args[i] in disabled_options):
            new_args.append(args[i]);
        i+=1;
    return (build_dir, " ".join(new_args));

def dump_rev_source(src_dir, src_file, arg_file, dump_file):
    (build_dir, build_arg) = parseArgFile(src_dir, arg_file);
    abs_src_file = path.abspath(src_dir + "/" + src_file);
    cmd = "clang " + build_arg + " -E " + abs_src_file + " -o " + dump_file;
    print cmd;
    ori_dir = os.getcwd();
    os.chdir(build_dir);
    ret = system(cmd);
    os.chdir(ori_dir);
    return ret == 0;

def diff(src_dir1, src_file1, arg_file1, src_dir2, src_file2, arg_file2):
    cmd = differ_cmd + " " + src_dir1 + " " + src_file1 + " " + src_dir2 + " " + \
        src_file2 + " -argf " +  arg_file1 + " -argf2 " + arg_file2 + " -print-diff-only ";
    ret = system(cmd);
    return (ret == 0);

if __name__ == "__main__":
    fulldir = path.abspath(path.dirname(argv[0]));
    differ_cmd = fulldir + "/../build/src/pdiffer";

    opts, args = getopt.getopt(argv[1:], "ay:j:", ["depdir=", "o-revs=", "i-revs=",
        "sid=", "eid=", "print-match", "dump-source="]);

    deps_dir = os.path.abspath("../build/benchmarks/php-deps");
    out_rev_file = "";
    in_rev_file = "";
    sid = 0;
    eid = 10000000;
    fix_only = True;
    year_limit = 2010;
    dump_dir = "";
    for o, a in opts:
        if o == "-a":
            fix_only = False;
        elif o == "-j":
            para = int(a);
        elif o == "-y":
            year_limit = int(a)
        elif o == "--depdir":
            deps_dir = a;
        elif o == "--o-revs":
            out_rev_file = a;
        elif o == "--i-revs":
            in_rev_file = a;
        elif o == "--sid":
            sid = int(a);
        elif o == "--eid":
            eid = int(a);
        elif o == "--dump-source":
            dump_dir = a;

    repo_dir = args[0];
    repo_type = args[1];
    repo = create_repo_handler(repo_dir, repo_type);
    build_cmd = args[2];
    rev_result_file = args[3];

    if in_rev_file == "":
        revs = repo.get_revs(fix_only, year_limit);
    else:
        fin = open(in_rev_file, "r");
        lines = fin.readlines();
        revs = [];
        for line in lines:
            tokens = line.strip().split();
            if (len(tokens) == 1):
                revs.append( (tokens[0], repo.get_parent_rev(tokens[0]), ""));
            else:
                revs.append( (tokens[0], tokens[1], "") );
        fin.close();

    if out_rev_file != "":
        fout = open(out_rev_file, "w");
        for rev, parent_rev, _ in revs:
            print >> fout, rev, parent_rev;
        fout.close();
        exit(0);

    if sid >= len(revs):
        print "sid is larger than the total number of revs, exit";
        exit(0);

    if eid > len(revs):
        eid = len(revs);

    tmp_dir = "__tmp";
    system("rm -rf " + tmp_dir);
    system("mkdir " + tmp_dir);
    tmp_repo1 = tmp_dir + "/src1";
    tmp_repo2 = tmp_dir + "/src2";
    system("cp -rf " + repo_dir + " " + tmp_repo1);
    system("cp -rf " + repo_dir + " " + tmp_repo2);
    system("rm -rf " + build_log);

    repo1 = create_repo_handler(tmp_repo1, repo_type);
    repo2 = create_repo_handler(tmp_repo2, repo_type);

    if dump_dir != "":
        system("rm -rf " + dump_dir);
        system("mkdir " + dump_dir);
        dump_dir = os.path.abspath(dump_dir);

    fout = open(rev_result_file, "w");
    total_cnt = 0;
    first = True;
    dump_failed = [];
    for i in range(sid, eid):
        (rev, parent_rev, _) = revs[i];
        print "Processing rev: ", rev;
        diff_res = repo.get_diff_for_c(parent_rev, rev);
        if (len(diff_res) == 0):
            print "No source file changed!";
            continue;
        # skip this revision becuase more than one files changed
        if (len(diff_res) > 1):
            print "Too many file modified!";
            continue;
        src_file = diff_res.keys()[0];
        if (not src_file.endswith(".c")):
            print "Modified file " + src_file + " not supported!";
            continue;
        print "src file: ", src_file;
        print "diff size: ", diff_res[src_file][0];
        repo1.switch_to_rev(parent_rev);
        repo2.switch_to_rev(rev);
        tmp_argfile_1 = tmp_dir + "/__arg1";
        tmp_argfile_2 = tmp_dir + "/__arg2";
        if not generate_arg_file(tmp_repo1, src_file, tmp_argfile_1, deps_dir, first):
            print "Built failed!";
            continue;

        if not generate_arg_file(tmp_repo2, src_file, tmp_argfile_2, deps_dir, first):
            print "Built failed!";
            continue;

        first = False;
        if (diff(tmp_repo1, src_file, tmp_argfile_1, tmp_repo2, src_file, tmp_argfile_2)):
            total_cnt += 1;
            if (dump_dir != ""):
                ret = dump_rev_source(tmp_repo1, src_file, tmp_argfile_1, dump_dir + "/" + rev + "-1.c");
                ret &= dump_rev_source(tmp_repo2, src_file, tmp_argfile_2, dump_dir + "/" + rev + "-2.c");
                if not ret:
                    system("rm -f " + dump_dir + "/" + rev + "-1.c");
                    system("rm -f " + dump_dir + "/" + rev + "-2.c");
                    dump_failed.append(rev);
                else:
                    system("cp -f " + tmp_argfile_1 + " " + dump_dir + "/" + rev + "-1.argf");
                    system("cp -f " + tmp_argfile_2 + " " + dump_dir + "/" + rev + "-2.argf");
                    print >>fout, rev;
            else:
                print >>fout, rev;
        #system("rm -rf " + tmp_argfile_1);
        #system("rm -rf " + tmp_argfile_2);
    fout.close();
    #system("rm -rf " + tmp_dir);
    print "Total 1 mod rev: ", total_cnt;
    if len(dump_failed) != 0:
        print "Failed dump revs:";
        for rev in dump_failed:
            print rev;
