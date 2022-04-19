#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config gmp.
grep -v '"tests/mpbsd/Makefile") ' configure |   sed "s#tests/mpbsd/Makefile ##g" |   sponge configure

PROJECT_CFLAGS="-g -O0  -static"

PROJECT_LDFLAGS=""
PROJECT_CONFIG_OPTIONS=" --disable-shared --enable-static \
            --disable-fft \
            --disable-mpbsd \
            --disable-cxx \
            --disable-fast-install \
            --disable-minithres "

if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi
if [[ -n "${CPPFLAGS}" ]]; then
  PROJECT_CPPFLAGS="${PROJECT_CPPFLAGS} ${CPPFLAGS}"
fi
if [[ -n "${LDFLAGS}" ]]; then
  PROJECT_LDFLAGS="${PROJECT_LDFLAGS} ${LDFLAGS}"
fi
if [[ -n "${CONFIG_OPTIONS}" ]]; then
  PROJECT_CONFIG_OPTIONS="${PROJECT_CONFIG_OPTIONS} ${CONFIG_OPTIONS}"
fi

make distclean
CC=gcc CXX=g++ ./configure CFLAGS="${PROJECT_CFLAGS}"
autoreconf --force --install
CC=gcc CXX=g++ ./configure CFLAGS="${PROJECT_CFLAGS}"  CXXFLAGS="${PROJECT_CXXFLAGS}" LDFLAGS="${PROJECT_LDFLAGS}" ${PROJECT_CONFIG_OPTIONS}
