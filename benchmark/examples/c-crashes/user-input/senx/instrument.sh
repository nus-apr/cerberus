#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1
mkdir $dir_name/senx

cd $dir_name/src

make clean
find . -name "*.cache" | xargs rm -rf
CC="wllvm" CXX="wllvm++" CFLAGS="-DFORTIFY_SOURCE=2 -fstack-protector-all -fno-omit-frame-pointer -Wno-error -g -O0" CXXFLAGS="$CFLAGS" make CXXFLAGS="$CFLAGS" -j`nproc`

binary_dir=$dir_name/src/
binary_name=test

extract-bc $binary_dir/$binary_name
analyze_bc $binary_dir/$binary_name.bc
cd $dir_name/senx
cp $binary_dir/$binary_name .
cp $binary_dir/$binary_name.bc .
cp $binary_dir/$binary_name.bc.talos .

llvm-dis $binary_name.bc
cp ../../../../../scripts/senx/prepare_gdb_script.py .
python3 prepare_gdb_script.py $binary_name
cp def_file $binary_dir
