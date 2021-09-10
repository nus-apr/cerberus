#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
src_dir_name=/experiment/$benchmark_name/$project_name/$fix_id/src
target_dir=/experiments/benchmark/$benchmark_name/$project_name/$fix_id


# Copy Seed Files
mkdir $target_dir/seed-dir
cp seed/* $target_dir/seed-dir

# Copy driver
cp driver.t  $src_dir_name/tests