#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config libtiff.
make clean
PATH_ORIG=$PATH
export PATH=/deps/php/bison-2.2-build/bin:$PATH_ORIG
./configure \
  --enable-cli \
  --disable-dom \
  --disable-libxml  \
  --disable-xml \
  --disable-simplexml \
  --disable-xmlreader  \
  --disable-xmlwriter  \
  --disable-pear  \
  --disable-inline-optimization  \
  --without-pcre-dir  \
  --disable-fileinfo \
  --disable-shared

export PATH=$PATH_ORIG

