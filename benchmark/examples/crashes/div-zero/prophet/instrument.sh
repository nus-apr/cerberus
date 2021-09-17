#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id

mkdir $dir_name/prophet
cp $script_dir/test.py $dir_name/prophet
cp $script_dir/tester_common.py $dir_name/prophet
cp $script_dir/build.py $dir_name/prophet
mkdir $dir_name/patched
cat <<EOF > $dir_name/prophet/prophet.conf
revision_file=/experiment/$benchmark_name/$project_name/$bug_id/prophet/prophet.revlog
src_dir=/experiment/$benchmark_name/$project_name/$bug_id/src
test_dir=/experiment/$benchmark_name/$project_name/$bug_id/tests
bugged_file=test.c
fixed_out_file=patched/$project_name-fix-$bug_id.c
build_cmd=$dir_name/prophet/build.py
test_cmd=$dir_name/prophet/test.py
localizer=profile
single_case_timeout=120
wrap_ld=yes
EOF

cat <<EOF > $dir_name/prophet/prophet.revlog
-
-
Diff Cases: Tot 1
7
Positive Cases: Tot 4
8 2 3 6
Regression Cases: Tot 0

EOF