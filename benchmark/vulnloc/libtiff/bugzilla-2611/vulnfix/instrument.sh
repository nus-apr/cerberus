#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/vulnfix

cd $dir_name/src

make clean
./configure
make CFLAGS="-static -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-static -fsanitize=address -fsanitize=undefined -g" -j`nproc`

config_path=$dir_name/vulnfix/config

cat > $config_path <<EOL
fix-location=tif_ojpeg.c:816
crash-location=tif_ojpeg.c:816
fix-file-path=libtiff/tif_ojpeg.c
fix-line=816
build-cmd=make clean && make CFLAGS="-static -fsanitize=address -fsanitize=undefined -g" CXXFLAGS="-static -fsanitize=address -fsanitize=undefined -g" -j10
EOL
