#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
POS_N=10
NEG_N=1

BINARY_PATH="$dir_name/src/gcd"
TEST_ID=$2

if [ -n "$3" ];
then
  BINARY_PATH=$3
fi


if [ -z "$TEST_ID" ]
then
   # Run passing test cases
  for i in `seq -s " " -f "p%g"  1 $POS_N`
  do
  bash $script_dir/test.sh $1 $i $BINARY_PATH
  done

  # Run failing test cases
  for i in `seq -s " " -f "n%g"  1 $NEG_N`
  do
  bash $script_dir/test.sh $1 $i $BINARY_PATH
  done
else
  pattern=`expr substr "$TEST_ID" 1 1`
  num=`expr substr "$TEST_ID" 2 ${#TEST_ID}`
  if [[ $pattern == 'n' ]]; then
      timeout 25 bash $script_dir/oracle-2 $1 $TEST_ID $BINARY_PATH
  elif [[ $pattern == 'p' ]]; then
      timeout 25 bash $script_dir/oracle-2 $1 $TEST_ID $BINARY_PATH
  else
      timeout 25 bash $script_dir/oracle-1 $1 $TEST_ID $BINARY_PATH
  fi

fi
