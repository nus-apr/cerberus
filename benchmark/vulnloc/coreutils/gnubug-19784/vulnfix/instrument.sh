#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/vulnfix

cd $dir_name/src

make clean

# for AFL argv fuzz
sed -i '29i #include "/home/yuntong/vulnfix/thirdparty/AFL/experimental/argv_fuzzing/argv-fuzz-inl.h"' src/make-prime-list.c
sed -i '175i AFL_INIT_SET0("./make-prime-list");' src/make-prime-list.c

./bootstrap
export FORCE_UNSAFE_CONFIGURE=1 && ./configure && make CFLAGS="-Wno-error -fsanitize=address -g" src/make-prime-list

config_path=$dir_name/vulnfix/config

cat > $config_path <<EOL
cmd=
fix-location=0x2d46
crash-location=0x2d46
input-from-stdin=true
fix-file-path=src/make-prime-list.c
fix-line=216
build-cmd=export FORCE_UNSAFE_CONFIGURE=1 && make clean && make CFLAGS="-Wno-error -fsanitize=address -g" src/make-prime-list
EOL
