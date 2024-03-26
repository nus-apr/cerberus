#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
TEST_CLASS=$1
EXIT_CODE=1
cd $dir_name/src

if [ -z "$TEST_CLASS" ];
then
  echo "requires a test class"
  exit 255
fi


timeout 20 mvn test -Drat.skip=true -Dtest=$TEST_CLASS > /dev/null 2>&1
EXIT_CODE=$?

if [[ EXIT_CODE -eq 0 ]]
then
  echo "PASS"
else
  echo "FAIL"
fi;

exit $EXIT_CODE