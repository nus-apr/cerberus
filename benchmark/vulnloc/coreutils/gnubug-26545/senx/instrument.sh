#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1
mkdir $dir_name/senx

cd $dir_name/src

make clean
export FORCE_UNSAFE_CONFIGURE=1 && CC="wllvm" CXX="wllvm++" CFLAGS="-g -O0" CXXFLAGS="$CFLAGS" ./configure
CC="wllvm" CXX="wllvm++" make CFLAGS="-g -O0 -static" CXXFLAGS="$CFLAGS" -j`nproc`
CC="wllvm" CXX="wllvm++" make CFLAGS="-g -O0 -static" CXXFLAGS="$CFLAGS" src/shred

binary_dir=$dir_name/src/src
binary_name=shred

extract-bc $binary_dir/$binary_name
cd $dir_name/senx
cp $binary_dir/$binary_name .
cp $binary_dir/$binary_name.bc .
analyze_bc $binary_name.bc
cp $binary_name.bc.talos $binary_dir

llvm-dis $binary_name.bc
cp ../../../../../scripts/senx/prepare_gdb_script.py .
python3 prepare_gdb_script.py $binary_name
cp def_file $binary_dir
