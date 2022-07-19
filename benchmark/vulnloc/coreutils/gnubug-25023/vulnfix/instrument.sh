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
echo a > $dummy_file

# for AFL argv fuzz
sed -i '856i #include "/home/yuntong/vulnfix/thirdparty/AFL/experimental/argv_fuzzing/argv-fuzz-inl.h"' src/pr.c
sed -i "860i AFL_INIT_SET0234(\"./pr\", \"$dummy_file\", \"-m\", \"$dummy_file\");" src/pr.c
# not bulding man pages
sed -i '229d' Makefile.am

./bootstrap
export FORCE_UNSAFE_CONFIGURE=1 && ./configure CFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g"
make CFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" -j`nproc`

config_path=$dir_name/vulnfix/config

cat > $config_path <<EOL
cmd=
fix-location=pr.c:1239
crash-location=pr.c:2243
input-from-stdin=true
fix-file-path=src/pr.c
fix-line=1238
build-cmd=make clean && make CFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-Wno-error -fsanitize=address -fsanitize=undefined -g" -j10
EOL
