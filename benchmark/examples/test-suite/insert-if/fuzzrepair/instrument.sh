#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

fix_file=$dir_name/src/$2

cd $dir_name/src
make clean
bear make CFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g " CXXFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g " LDFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g" -j`nproc`

cd $LIBPATCH_DIR/rewriter
./rewritecond $fix_file -o $fix_file
ret=$?
if [[ ret -eq 1 ]]
then
   exit 128
fi

cd $dir_name/src/
make CFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g " CXXFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g " LDFLAGS="-ldl -fsanitize=address -Wno-error -O0 -g" -j`nproc`
