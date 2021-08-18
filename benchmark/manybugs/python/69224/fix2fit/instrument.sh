#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
src_dir_name=/data/$benchmark_name/$project_name/$fix_id/src
test_dir_name=/data/$benchmark_name/$project_name/$fix_id/test
exp_dir_name=/data/$benchmark_name/$project_name/$fix_id
target_dir=/experiments/benchmark/$benchmark_name/$project_name/$fix_id
cd $test_dir_name

# Copy Seed Files
mkdir $target_dir/seed-dir
find . -type f -iname 'test_*.py' -exec cp  {} $target_dir/seed-dir/ \;

cd $exp_dir_name
sed -i "11d" python-run-tests.pl
sed -i "s/run_test 243/run_test 244/" test.sh
sed -i "s/n1\) run_test 244/n1\) run_test 243/" test.sh
make clean

if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi

sed -i 's/T_TIMEOUT=50000/T_TIMEOUT=300000/' /src/scripts/run.sh