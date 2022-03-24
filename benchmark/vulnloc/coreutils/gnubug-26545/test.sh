#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
BINARY_PATH="$dir_name/src/src/shred"
TEST_ID=$2

if [ -n "$3" ];
then
  BINARY_PATH=$3
fi


case "$2" in
    1)
        POC=$script_dir/tests/1.txt
        export ASAN_OPTIONS=detect_leaks=0,halt_on_error=0
        timeout 10 $BINARY_PATH -n4 -s7 $POC > $BINARY_PATH.out 2>&1
        ret=$?
        if [[ ret -eq 0 ]]
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
        fi;
esac

