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
import getopt
from os import chdir, getcwd, system, path, environ
import subprocess

cases = [
    "tests/t-bswap",
    "tests/t-constants",
    "tests/t-count_zeros",
    "tests/t-gmpmax",
    "tests/t-hightomask",
    "tests/t-modlinv",
    "tests/t-popc",
    "tests/t-parity",
    "tests/t-sub",
    "tests/mpz/t-addsub",
    "tests/mpz/t-cmp",
    "tests/mpz/t-mul",
    "tests/mpz/t-mul_i",
    "tests/mpz/t-tdiv",
    "tests/mpz/t-tdiv_ui",
    "tests/mpz/t-fdiv",
    "tests/mpz/t-fdiv_ui",
    "tests/mpz/t-cdiv_ui",
    "tests/mpz/t-gcd",
    "tests/mpz/t-gcd_ui",
    "tests/mpz/t-lcm",
    "tests/mpz/dive",
    "tests/mpz/dive_ui",
    "tests/mpz/t-sqrtrem",
    "tests/mpz/convert",
    "tests/mpz/io",
    "tests/mpz/t-inp_str",
    "tests/mpz/logic",
    "tests/mpz/bit",
    "tests/mpz/t-powm",
    "tests/mpz/t-powm_ui",
    "tests/mpz/t-pow",
    "tests/mpz/t-div_2exp",
    "tests/mpz/reuse",
    "tests/mpz/t-root",
    "tests/mpz/t-perfsqr",
    "tests/mpz/t-perfpow",
    "tests/mpz/t-jac",
    "tests/mpz/t-bin",
    "tests/mpz/t-get_d",
    "tests/mpz/t-get_d_2exp",
    "tests/mpz/t-get_si",
    "tests/mpz/t-set_d",
    "tests/mpz/t-set_si",
    "tests/mpz/t-fac_ui",
    "tests/mpz/t-fib_ui",
    "tests/mpz/t-lucnum_ui",
    "tests/mpz/t-scan",
    "tests/mpz/t-fits",
    "tests/mpz/t-divis",
    "tests/mpz/t-divis_2ecounter",
    "tests/mpz/t-cong",
    "tests/mpz/t-cong_2exp",
    "tests/mpz/t-sizeinbase",
    "tests/mpz/t-set_str",
    "tests/mpz/t-aorsmul",
    "tests/mpz/t-cmp_d",
    "tests/mpz/t-cmp_si",
    "tests/mpz/t-hamdist",
    "tests/mpz/t-oddeven",
    "tests/mpz/t-popcount",
    "tests/mpz/t-set_f",
    "tests/mpz/t-io_raw",
    "tests/mpz/t-import",
    "tests/mpz/t-export",
    "tests/mpz/t-pprime_p",
    "tests/mpz/t-nextprime",
    "tests/mpf/t-add",
    "tests/mpf/t-sub",
    "tests/mpf/t-conv",
    "tests/mpf/t-sqrt",
    "tests/mpf/t-sqrt_ui",
    "tests/mpf/t-muldiv",
    "tests/mpf/t-dm2exp",
    "tests/mpf/reuse",
    "tests/mpf/t-cmp_d",
    "tests/mpf/t-cmp_si",
    "tests/mpf/t-div",
    "tests/mpf/t-fits",
    "tests/mpf/t-get_d",
    "tests/mpf/t-get_d_2exp",
    "tests/mpf/t-get_si",
    "tests/mpf/t-get_ui",
    "tests/mpf/t-gsprec",
    "tests/mpf/t-inp_str",
    "tests/mpf/t-int_p",
    "tests/mpf/t-mul_ui",
    "tests/mpf/t-set",
    "tests/mpf/t-set_q",
    "tests/mpf/t-set_si",
    "tests/mpf/t-set_ui",
    "tests/mpf/t-trunc",
    "tests/mpf/t-ui_div",
    "tests/mpf/t-eq",
    "tests/misc/t-printf",
    "tests/misc/t-scanf",
    "tests/misc/t-locale",
    "tests/mpq/t-aors",
    "tests/mpq/t-cmp",
    "tests/mpq/t-cmp_ui",
    "tests/mpq/t-cmp_si",
    "tests/mpq/t-equal",
    "tests/mpq/t-get_d",
    "tests/mpq/t-get_str",
    "tests/mpq/t-inp_str",
    "tests/mpq/t-md_2exp",
    "tests/mpq/t-set_f",
    "tests/mpq/t-set_str",
    "tests/rand/t-iset",
    "tests/rand/t-lc2exp",
    "tests/rand/t-mt",
    "tests/rand/t-rand",
    "tests/rand/t-urbui",
    "tests/rand/t-urmui",
    "tests/rand/t-urndmm",
    "tests/mpn/t-asmtype",
    "tests/mpn/t-aors_1",
    "tests/mpn/t-divrem_1",
    "tests/mpn/t-mod_1",
    "tests/mpn/t-fat",
    "tests/mpn/t-get_d",
    "tests/mpn/t-instrument",
    "tests/mpn/t-iord_u",
    "tests/mpn/t-mp_bases",
    "tests/mpn/t-perfsqr",
    "tests/mpn/t-scan",
    "tests/mpn/t-toom22",
    "tests/mpn/t-toom32",
    "tests/mpn/t-toom33",
    "tests/mpn/t-toom42",
    "tests/mpn/t-toom43",
    "tests/mpn/t-toom44",
    "tests/mpn/t-toom52",
    "tests/mpn/t-toom53",
    "tests/mpn/t-toom62",
    "tests/mpn/t-toom63",
    "tests/mpn/t-toom6h",
    "tests/mpn/t-toom8h",
    "tests/mpn/t-hgcd",
    "tests/mpn/t-matrix22",
    "tests/mpn/t-mullo",
    "tests/mpn/t-mulmod_bnm1",
    "tests/mpn/t-sqrmod_bnm1",
    "tests/mpn/t-invert",
    "tests/mpn/t-div",
    "tests/mpn/t-bdiv"];

if __name__ == "__main__":
    opts, args = getopt.getopt(argv[1 :], "p:");
    profile_dir = "";
    for o, a in opts:
        if o == "-p":
            profile_dir = a;

    src_dir = args[0];
    test_dir = args[1];
    work_dir = args[2];

    if (len(args) > 3):
        ids = args[3 :];
        cur_dir = src_dir;
        if (profile_dir != ""):
            cur_dir = profile_dir;

        if (not path.exists(cur_dir + "/mytests")):
            system("cp -rf " + test_dir + " " + cur_dir + "/mytests");

        ori_dir = getcwd();
        my_env = environ;
        for i in ids:
            case_str = cases[int(i) - 1];
            tokens = case_str.split("/");
            assert( tokens[0] == "tests");
            if (len(tokens) == 3):
                subdir = cur_dir + "/mytests/" + tokens[1];
                testfile = tokens[2];
            else:
                assert(len(tokens) == 2);
                subdir = cur_dir + "/mytests";
                testfile = tokens[1];
            chdir(subdir);
            system("rm -f " + testfile + ".log");
            ret = subprocess.call(["make " + testfile + " >/dev/null 2>/dev/null"], shell = True);
            if (ret != 0):
                chdir(ori_dir);
                continue;
            ret = subprocess.call(["./" + testfile + " >/dev/null 2>/dev/null"], shell = True);
            if (ret == 0):
                print i,
            chdir(ori_dir);
