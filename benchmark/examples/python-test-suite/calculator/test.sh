#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
dir_test=$dir_name/src
TEST_ID=$1
EXIT_CODE=1

if [ ! -d "$dir_test" ]; then
  echo "$dir_test does not exist."
  exit 123
fi

if [ -z "$(ls -A $dir_test/*test*.py)" ]; then
  echo "$dir_test is empty"
  exit 123
fi

if [ -z "$TEST_ID" ];
then
  cd $dir_test
  for x in $dir_test/*test*.py;
  do
    pytest $(basename $x) > /dev/null 2>&1
    EXIT_CODE=$?
    if [[ EXIT_CODE -ne 0 ]]
    then
      echo "FAIL", $x
      break
    else
      echo "PASS", $x
    fi;
  done
  exit $EXIT_CODE
fi

TEST_FILE=${TEST_ID}.py

TEST_CASE=$dir_test/${TEST_FILE}

if [ -f "$TEST_CASE" ]; then
    cd $dir_test
    pytest ${TEST_FILE} > /dev/null 2>&1
    EXIT_CODE=$?
else
    echo "unknown test case"
    exit 255
fi

if [[ EXIT_CODE -eq 0 ]]
then
  echo "PASS"
else
  echo "FAIL"
fi;

exit $EXIT_CODE