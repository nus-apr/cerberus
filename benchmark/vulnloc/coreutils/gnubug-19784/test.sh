#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
BINARY_PATH="$dir_name/src/src/make-prime-list"
TEST_ID=$1

if [ -n "$2" ];
then
  BINARY_PATH=$2
fi


case "$1" in
    1)
        POC="15"
        timeout 25 $BINARY_PATH $POC
esac

