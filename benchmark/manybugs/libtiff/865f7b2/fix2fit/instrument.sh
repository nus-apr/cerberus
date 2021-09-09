#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
src_dir_name=$1/experiments/$benchmark_name/$project_name/$fix_id/src
target_dir=/experiments/benchmark/$benchmark_name/$project_name/$fix_id
cd $src_dir_name/test

# Copy Seed Files
mkdir $target_dir/seed-dir
find . -type f -iname '*.tiff' -exec cp  {} $target_dir/seed-dir/ \;
find . -type f -iname '*.bmp' -exec cp  {} $target_dir/seed-dir/ \;
find . -type f -iname '*.gif' -exec cp  {} $target_dir/seed-dir/ \;
find . -type f -iname '*.pgm' -exec cp  {} $target_dir/seed-dir/ \;
find . -type f -iname '*.ppm' -exec cp  {} $target_dir/seed-dir/ \;
find . -type f -iname '*.pbm' -exec cp  {} $target_dir/seed-dir/ \;

if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi