#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
src_dir_name=$dir_name/src
cd $src_dir_name/test

# Copy Seed Files
mkdir $dir_name/seed-dir
find . -type f -iname '*.tiff' -exec cp  {} $dir_name/seed-dir/ \;
find . -type f -iname '*.bmp' -exec cp  {} $dir_name/seed-dir/ \;
find . -type f -iname '*.gif' -exec cp  {} $dir_name/seed-dir/ \;
find . -type f -iname '*.pgm' -exec cp  {} $dir_name/seed-dir/ \;
find . -type f -iname '*.ppm' -exec cp  {} $dir_name/seed-dir/ \;
find . -type f -iname '*.pbm' -exec cp  {} $dir_name/seed-dir/ \;

cd $src_dir_name

if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi

CC=f1x-cc CXX=f1x-cxx $script_dir/../config.sh $1
CC=f1x-cc CXX=f1x-cxx $script_dir/../build.sh $1