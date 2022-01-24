#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1
mkdir $dir_name/senx

cd $dir_name/src

make clean
CC=wllvm CXX=wllvm++ FORCE_UNSAFE_CONFIGURE=1 ./configure CFLAGS='-g -O0' CXXFLAGS="$CFLAGS"
CC=wllvm CXX=wllvm++ make CFLAGS="-g -O0 -static" CXXFLAGS="$CFLAGS" -j32

extract-bc $dir_name/src/src/split
cd $dir_name/senx
cp $dir_name/src/src/split.bc .
analyze_bc split.bc
cp split.bc.talos $dir_name/src/src/
