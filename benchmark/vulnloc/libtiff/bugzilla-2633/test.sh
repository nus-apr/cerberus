#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

TEST_ID=$2
BINARY_PATH="$dir_name/src/tools/tiff2ps"


if [ -n "$3" ];
then
  BINARY_PATH=$3
fi


case "$2" in
    1)
        POC=$script_dir/tests/1.tif
        timeout 10 $BINARY_PATH $POC > $BINARY_PATH.out 2>&1 ;;
esac

ret=$?
if [[ ret -eq 1 ]]
then
   err=$(cat $BINARY_PATH.out | grep 'AddressSanitizer'  | wc -l)
    if [[ err -eq 0 ]]
    then
      exit 0
    else
      exit 128
    fi;
else
   exit $ret
fi