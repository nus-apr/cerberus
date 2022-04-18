#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src
sed -i '978 s/./\t&/' test/Makefile
# Compile libtiff.
PROJECT_CFLAGS="-g -O0 -static -march=x86-64"
PROJECT_LDFLAGS="-static"


if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi

if [[ -n "${LDFLAGS}" ]]; then
  PROJECT_LDFLAGS="${PROJECT_LDFLAGS} ${LDFLAGS}"
fi

make -e CFLAGS="${PROJECT_CFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}" -j`nproc`

cd test
rm -f long_tag
make -e long_tag -j`nproc`
rm -f short_tag
make -e short_tag -j`nproc`
rm -f strip_rw
make -e strip_rw -j`nproc`