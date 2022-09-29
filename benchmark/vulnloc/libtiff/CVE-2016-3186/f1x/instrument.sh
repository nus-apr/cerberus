#!/bin/bash
apt update && apt install -y liblzma-dev libjpeg-dev
 
cd ..

script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

cd $dir_name/src
make distclean

PROJECT_CFLAGS="-g -O0 -static"
if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi

PROJECT_CONFIG_OPTIONS=" --enable-static --disable-shared"
if [[ -n "${CONFIG_OPTIONS}" ]]; then
  PROJECT_CONFIG_OPTIONS="${PROJECT_CONFIG_OPTIONS} ${CONFIG_OPTIONS}"
fi

 ./configure CC=f1x-cc CXX=f1x-cxx CFLAGS="${PROJECT_CFLAGS}" ${PROJECT_CONFIG_OPTIONS}