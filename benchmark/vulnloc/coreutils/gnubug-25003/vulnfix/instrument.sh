#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/vulnfix

cd $dir_name/src

make clean

dummy_file=$dir_name/vulnfix/dummy
touch $dummy_file

# for AFL argv fuzz
sed -i '1283i #include "/home/yuntong/vulnfix/thirdparty/AFL/experimental/argv_fuzzing/argv-fuzz-inl.h"' src/split.c
sed -i "1288i AFL_INIT_SET02("./split", "$dummy_file");" src/split.c
# avoid writing out a lot of files during fuzzing
sed -i '595i return false;' src/split.c
# not bulding man pages
sed -i '229d' Makefile.am

./bootstrap
export FORCE_UNSAFE_CONFIGURE=1 && ./configure
make CFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" -j`nproc`

config_path=$dir_name/vulnfix/config

cat > $config_path <<EOL
cmd=
fix-location=split.c:988
crash-location=split.c:988
input-from-stdin=true
fix-file-path=src/split.c
fix-line=986
build-cmd=make clean && make CFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" -j10
EOL
