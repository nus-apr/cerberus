#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$fix_id
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name

project_url=https://sourceware.org/git/binutils-gdb.git
commit_id=515f23e63c0074ab531bc954f84ca40c6281a724

cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id


