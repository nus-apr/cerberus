#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id

current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
mkdir dev-patch

project_url=https://github.com/vadz/libtiff.git
fix_commit_id=5ed9fea523316c2f5cec4d393e4d5d671c2dbc33
bug_commit_id=f3069a5

cd $dir_name
git clone $project_url src
cd src
git checkout $bug_commit_id
git format-patch -1 $fix_commit_id
cp *.patch $dir_name/dev-patch

./autogen.sh
