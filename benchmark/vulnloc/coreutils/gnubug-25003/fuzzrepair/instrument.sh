#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

# first copy over a pre-instrumented version of fix file
cp $script_dir/split.c $fix_file

cd $dir_name/src

# for AFL argv fuzz
sed -i "1435i #include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"" src/split.c
# dummy is just an empty file
sed -i "1440i AFL_INIT_SET02(\"./split\", \"${dir_name}/src/dummy\");" src/split.c
# not bulding man pages
sed -i '229d' Makefile.am

$script_dir/../config.sh $1
cd $dir_name/src
# create a dummy file; this path must match the one in instrumentation
touch dummy
# do make 
make clean

$script_dir/../build.sh $1
