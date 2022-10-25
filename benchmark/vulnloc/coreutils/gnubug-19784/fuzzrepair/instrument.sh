#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

cd $dir_name/src

# for AFL argv fuzz
sed -i "29i #include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"" src/make-prime-list.c
sed -i '175i AFL_INIT_SET0("./make-prime-list");' src/make-prime-list.c

$script_dir/../config.sh $1
cd $dir_name/src
make clean
bear $script_dir/../build.sh $1
# comment out this for rewriter to work
sed -i "s|#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|//#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|g" src/make-prime-list.c

cd $LIBPATCH_DIR/rewriter
./rewritecond $fix_file -o $fix_file
ret=$?
if [[ ret -eq 1 ]]
then
   exit 128
fi
# change back
cd $dir_name/src
sed -i "s|//#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|#include \"${LIBPATCH_DIR}/helpers/argv-fuzz-inl.h\"|g" src/make-prime-list.c

$script_dir/../build.sh $1
