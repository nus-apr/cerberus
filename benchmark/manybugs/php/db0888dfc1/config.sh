#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config PHP.
make clean


PROJECT_CFLAGS=""
if [[ -n "${CFLAGS}" ]]; then
  PROJECT_CFLAGS="${PROJECT_CFLAGS} ${CFLAGS}"
fi

PROJECT_CONFIG_OPTIONS="  --enable-cli \
  --disable-dom \
  --disable-libxml  \
  --disable-xml \
  --disable-simplexml \
  --disable-xmlreader  \
  --disable-xmlwriter  \
  --disable-pear  \
  --disable-phar \
  --disable-inline-optimization  \
  --without-pcre-dir  \
  --disable-fileinfo \
  --disable-shared "

if [[ -n "${CONFIG_OPTIONS}" ]]; then
  PROJECT_CONFIG_OPTIONS="${PROJECT_CONFIG_OPTIONS} ${CONFIG_OPTIONS}"
fi

./configure CFLAGS="${PROJECT_CFLAGS}" ${PROJECT_CONFIG_OPTIONS}


