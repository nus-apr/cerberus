#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


# copy test cases
cp -rf $dir_name/src/tests $script_dir/test-suite/

# copy libraries
cp -rf $dir_name/src/src/.libs $script_dir/test-suite/src
cp -rf $dir_name/src/src/*.la $script_dir/test-suite/src


cd $dir_name/src
driver_list=($(find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'  | grep -v ".so" ))
for i in "${driver_list[@]}"
do
  driver_path=${i::-1}
  directories=$(dirname $driver_path)
  driver_name=$(basename $driver_path)
  mkdir -p $script_dir/test-suite/$directories
  cp $script_dir/test-suite/template $script_dir/test-suite/$directories/$driver_name
  cp $driver_path $script_dir/test-suite/$directories/$driver_name.orig
  sed -i "s#TEMP#$driver_name#g" $script_dir/test-suite/$directories/$driver_name
done



