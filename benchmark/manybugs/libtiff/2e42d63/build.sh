#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$bug_id
cd $dir_name/src
sed -i '978 s/./\t&/' test/Makefile
# Compile libtiff.
make -e  CFLAGS="-march=x86-64" -j`nproc`
cd test
rm -f long_tag
make -e long_tag -j`nproc`
rm -f short_tag
make -e short_tag -j`nproc`
rm -f strip_rw
make -e strip_rw -j`nproc`