#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/vulnfix
cd $dir_name/src
make clean
make CFLAGS="-fsanitize=address -fsanitize=undefined -g" CXXFLAGS=" -fsanitize=address -fsanitize=undefined -g" -j`nproc`


config_path=$script_dir/config
cd $dir_name/vulnfix

cat <<EOF > $config_path
fix-location=test.c:19
crash-location=test.c:4
fix-file-path=test.c
fix-line=19
build-cmd=make clean && make CFLAGS="-fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-fsanitize=address -fsanitize=undefined -g" -j10
EOF

cp $config_path $dir_name/vulnfix


