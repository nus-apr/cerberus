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
test_dir=/experiment/$benchmark_name/$project_name/$fix_id/src/tests
bugged_file=mpz/gcdext.c
fixed_out_file=patches/$project_name-fix-$fix_id.c
build_cmd=$script_dir/build.sh
test_cmd="$script_dir/test.sh /experiment"
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