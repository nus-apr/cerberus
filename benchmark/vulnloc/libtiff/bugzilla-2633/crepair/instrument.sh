#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


cat <<EOF > repair.conf
dir_exp:$dir_name
tag_id:$bug_id
src_directory:$dir_name/src
binary_path:$dir_name/src/tools/tiff2ps
config_command:CC=crepair-cc ./configure CFLAGS="-g -O0" --enable-static --disable-shared
build_command:make CC=crepair-cc CXX=crepair-cxx CFLAGS="-g -O0 -static" CXXFLAGS="-g -O0 -static" LDFLAGS="-static"
test_input_list:\$POC
poc_list:$script_dir/../tests/1.tif
klee_flags:--link-llvm-lib=/CrashRepair/lib/libcrepair_proxy.bca
EOF

cd $dir_name/src
sed -i 's/fabs/fabs_trident/g' libtiff/tif_luv.c
sed -i 's/fabs/fabs_trident/g' tools/tiff2ps.c
git add  libtiff/tif_luv.c tools/tiff2ps.c
git config --global user.email "you@example.com"
git config --global user.name "Your Name"
git commit -m 'replace fabs with proxy function'

