#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

cd $dir_name/src

PROJECT_CFLAGS="-g -O0 -static"
PROJECT_CPPFLAGS="-g -O0 -static"
PROJECT_LDFLAGS="-static"

if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi
if [[ -n "${CPPFLAGS}" ]]; then
  PROJECT_CPPFLAGS="${PROJECT_CPPFLAGS} ${CPPFLAGS}"
fi
if [[ -n "${LDFLAGS}" ]]; then
  PROJECT_LDFLAGS="${PROJECT_LDFLAGS} ${LDFLAGS}"
fi

PROJECT_CONFIG_OPTIONS=" --enable-static --disable-shared"
if [[ -n "${CONFIG_OPTIONS}" ]]; then
  PROJECT_CONFIG_OPTIONS="${PROJECT_CONFIG_OPTIONS} ${CONFIG_OPTIONS}"
fi

 ./configure CFLAGS="${PROJECT_CFLAGS}" CPPFLAGS="${PROJECT_CPPFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}" ${PROJECT_CONFIG_OPTIONS}
