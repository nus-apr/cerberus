#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


# copy test driver
cp $dir_name/tester.py $script_dir/test-suite
cp $dir_name/tests.all.txt $script_dir/test-suite
cp $dir_name/src/run-tests.php $script_dir/test-suite


cd $dir_name/src

# copy test cases
cd $dir_name/src
test_list=($(find -name "*.phpt"))
for t in "${test_list[@]}"
do
  directories=$(dirname $t)
  test_name=$(basename $t)
  mkdir -p $script_dir/test-suite/$directories
  cp $t $script_dir/test-suite/$directories
done

driver_list=("sapi/cli/php")
for i in "${driver_list[@]}"
do
  driver_path=$i
  directories=$(dirname $driver_path)
  driver_name=$(basename $driver_path)
  mkdir -p $script_dir/test-suite/$directories
  cp $script_dir/test-suite/template $script_dir/test-suite/$directories/$driver_name
  cp $driver_path $script_dir/test-suite/$directories/$driver_name.orig
  sed -i "s#TEMP#$driver_name#g" $script_dir/test-suite/$directories/$driver_name
done

