#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$bug_id
cd $dir_name
TEST_ID=$1
POS_N=292
NEG_N=1



if [ -z "$TEST_ID" ]
then
   # Run passing test cases
  for i in `seq -s " " -f "p%g"  1 $POS_N`
  do
  bash test.sh $i /data
  done

  # Run failing test cases
  for i in `seq -s " " -f "n%g"  1 $NEG_N`
  do
  bash test.sh $i /data
  done
else
  pattern=`expr substr "$TEST_ID" 1 1`
  num=`expr substr "$TEST_ID" 2 ${#TEST_ID}`

  if [[ $pattern == 'n' ]]; then
      cd $dir_name
      timeout 300 bash test.sh $TEST_ID
  elif [[ $pattern == 'p' ]]; then
      cd $dir_name
      timeout 300 bash test.sh $TEST_ID
  else
      cd $dir_name/src
      if [[ $TEST_ID == '195' ]]; then
         TEST_ID=194
      fi
      timeout 300 perl $dir_name/${project_name}-run-tests.pl $TEST_ID
      ret=$?
      if [[ $ret == 0 ]]; then
         exit 0;
      fi
      exit 1;
  fi

fi