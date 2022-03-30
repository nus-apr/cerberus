#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$fix_id

mkdir $dir_name/prophet

mkdir $dir_name/patches
cat <<EOF > $dir_name/prophet/prophet.conf
revision_file=/experiment/$benchmark_name/$project_name/$fix_id/prophet/prophet.revlog
src_dir=/experiment/$benchmark_name/$project_name/$fix_id/src
test_dir=/experiment/$benchmark_name/$project_name/$fix_id/src/test
bugged_file=tools/tiff2pdf.c
fixed_out_file=patches/$project_name-fix-$fix_id.c
build_cmd=/prophet-gpl/tools/$project_name-build.py
test_cmd=/prophet-gpl/tools/$project_name-test.py
dep_dir=/prophet-gpl/benchmarks/$project_name-deps
localizer=profile
single_case_timeout=120
wrap_ld=yes
EOF

cat <<EOF > $dir_name/prophet/prophet.revlog
-
-
Diff Cases: Tot 1
28
Positive Cases: Tot 75
1 2 3 4 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78
Regression Cases: Tot 0

EOF



