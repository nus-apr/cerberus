#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
src_dir_name=/experiment/$benchmark_name/$project_name/$fix_id/src
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

cd $src_dir_name



if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi


## Instrument Short_TAG
sed -i '43d ' test/short_tag.c
sed -i '43i const char      *filename = "short_test.tiff";' test/short_tag.c
sed -i '81i main(int argc, char** argv)' test/short_tag.c
sed -i '82d' test/short_tag.c
sed -i '151i \\tfilename = argv[1];'  test/short_tag.c


cd test
make -j32 long_tag.log short_tag.log