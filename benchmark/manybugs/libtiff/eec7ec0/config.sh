#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config libtiff.
make clean
./configure CFLAGS='-g -O0' --enable-static --disable-shared \
            --disable-nls                                 \
            --disable-shared                              \
            --disable-cxx                                 \
            --disable-jpeg                                \
            --disable-zlib                                \
            --disable-pixarlog                            \
            --disable-jbig;

