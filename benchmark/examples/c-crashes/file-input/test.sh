#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
cd $dir_name
TEST_ID=$1
BINARY_PATH=$dir_name/src/test
POC=$script_dir/tests/$TEST_ID
timeout 10 $BINARY_PATH $POC
ret=$?
if [[ ret -eq 1 ]]
then
   exit 0;
else
   exit $ret
fi;