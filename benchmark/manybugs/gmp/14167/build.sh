#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src


sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
# Compile gmp


PROJECT_CFLAGS="-g -O0 -static"

if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi

if [[ -n "${LDFLAGS}" ]]; then
  PROJECT_LDFLAGS="${PROJECT_LDFLAGS} ${LDFLAGS}"
fi

make -e fib_table.h;make -e mp_bases.h;
make -e CFLAGS="${PROJECT_CFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}" -j`nproc`
cd tests/mpz
make -e CFLAGS="${PROJECT_CFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}"  t-gcd