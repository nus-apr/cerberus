#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

# build all drivers
bash test.sh $1

cd $dir_name/src/tests
driver_list=($(find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'))
for i in "${driver_list[@]}"
do
  driver_path=${i::-1}
  directories=$(dirname $driver_path)
  driver_name=$(basename $driver_path)
  mkdir -p $dir_name/test-suite/tests/$directories
  cp $dir_name/test-suite/template $dir_name/test-suite/tests/$directories/$driver_name
  cp $driver_path $dir_name/test-suite/tests/$directories/$driver_name.orig
  sed -i "s#TEMP#$driver_name#g" $dir_name/test-suite/tests/$directories/$driver_name
done


# copy binary executables
#find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'
cp -f $dir_name/src/gzip test-suite/gzip.orig

# copy test cases
cp -rf $dir_name/src/tests test-suite

# update path for test case
sed -i 's#/experiment//manybugs/gzip/$bug_id/src/tests#/tmp#g' test-suite/tests/hufts


