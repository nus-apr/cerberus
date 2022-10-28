#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

# first copy over a pre-instrumented version of fix file
cp $script_dir/pr.c $fix_file

cd $dir_name/src

# for AFL argv fuzz
sed -i "864i #include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"" src/pr.c
sed -i "869i AFL_INIT_SET0234(\"./pr\", \"${dir_name}/src/dummy\", \"-m\", \"${dir_name}/src/dummy\");" src/pr.c
# not bulding man pages
sed -i '229d' Makefile.am

$script_dir/../config.sh $1
cd $dir_name/src
# create dummy file - this one much match the path in instrumentation
echo a > dummy
# do make
make clean
$script_dir/../build.sh $1
