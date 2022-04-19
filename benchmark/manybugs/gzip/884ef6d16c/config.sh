#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config libtiff.
make clean
PROJECT_CFLAGS="-g -O0 "
PROJECT_CXXFLAGS="-g -O0 "
PROJECT_LDFLAGS=""


if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi
if [[ -n "${CPPFLAGS}" ]]; then
  PROJECT_CPPFLAGS="${PROJECT_CPPFLAGS} ${CPPFLAGS}"
fi
if [[ -n "${LDFLAGS}" ]]; then
  PROJECT_LDFLAGS="${PROJECT_LDFLAGS} ${LDFLAGS}"
fi

 ./configure CFLAGS="${PROJECT_CFLAGS}"  CXXFLAGS="${PROJECT_CXXFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}"

