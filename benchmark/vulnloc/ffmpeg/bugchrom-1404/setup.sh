#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
mkdir dev-patch

apt install clang -y

project_url=https://github.com/FFmpeg/FFmpeg.git
fix_commit_id=279420b5a63b3f254e4932a4afb91759fb50186a
bug_commit_id=1e42736

cd $dir_name
git clone $project_url src
cd src
git checkout $bug_commit_id
git format-patch -1 $fix_commit_id
cp *.patch $dir_name/dev-patch/fix.patch
cp $script_dir/configure $dir_name/src
cp $script_dir/Makefile $dir_name/src
cp $script_dir/deps/afl_driver.cpp $dir_name/src

cd $script_dir/deps
./build_ffmpeg.sh


