#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

# first copy over a pre-instrumented version of fix file
cp $script_dir/shred.c $fix_file

cd $dir_name/src

# not bulding man pages
sed -i '217d' Makefile.am
# remove and recreate output so that it does not grow too big.
sed -i '1370i FILE* file_ptr = fopen(file[i], "w"); fclose(file_ptr);' src/shred.c
# -u option can cause a lot of files to be writting to disk during fuzzing; disable that
sed -i '1309i break;' src/shred.c
# for AFL argv fuzz
sed -i "1268i AFL_INIT_SET03(\"./shred\", \"${dir_name}/src/dummy\");" src/shred.c
sed -i "1264i #include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"" src/shred.c


$script_dir/../config.sh $1
cd $dir_name/src
# create dummy file - this needs to be the same as path in instrumentation
touch dummy
# do make
make clean
$script_dir/../build.sh $1
