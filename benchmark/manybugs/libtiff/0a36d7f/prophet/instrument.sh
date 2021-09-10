#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$fix_id

mkdir $dir_name/prophet

cat <<EOF > $dir_name/prophet/prophet.conf
revision_file=/experiment/$benchmark_name/$project_name/$fix_id/prophet/prophet.revlog
src_dir=/experiment/$benchmark_name/$project_name/$fix_id/src
test_dir=/experiment/$benchmark_name/$project_name/$fix_id/src/test
bugged_file=libtiff/tif_dirread.c
fixed_out_file=$project_name-fix-$fix_id.c
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
Diff Cases: Tot 5
2 3 4 22 23
Positive Cases: Tot 30
6 7 8 9 10 11 12 13 14 15 16 17 19 20 21 24 25 26 27 28 73
Regression Cases: Tot 0

EOF



