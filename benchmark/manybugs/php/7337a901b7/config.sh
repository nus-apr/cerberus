#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/experiments/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config libtiff.
make clean
PHP_AUTOHEADER=/usr/bin/autoheader PHP_AUTOCONF=/usr/bin/autoconf ./buildconf
./configure \
  --enable-cli \
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
  --disable-shared



