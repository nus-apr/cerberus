#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

cd $dir_name/src

# for AFL argv fuzz
sed -i "1283i #include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"" src/split.c
# dummy is just an empty file
sed -i "1288i AFL_INIT_SET02(\"./split\", \"${dir_name}/src/dummy\");" src/split.c
# avoid writing out a lot of files during fuzzing
sed -i '595i return false;' src/split.c
# not bulding man pages
sed -i '229d' Makefile.am

$script_dir/../config.sh $1
cd $dir_name/src
# create a dummy file; this path must match the one in instrumentation
touch dummy
# do make 
make clean
bear $script_dir/../build.sh $1
# comment out this for rewriter to work
sed -i "s|#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|//#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|g" src/split.c

cd $LIBPATCH_DIR/rewriter
./rewritecond $fix_file -o $fix_file
ret=$?
if [[ ret -eq 1 ]]
then
   exit 128
fi
# change back
cd $dir_name/src
sed -i "s|//#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|g" src/split.c

$script_dir/../build.sh $1
