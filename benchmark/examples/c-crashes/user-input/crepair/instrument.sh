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
binary_path:$dir_name/src/test
config_command:make clean && CC=crepair-cc make CFLAGS="-DFORTIFY_SOURCE=2 -fstack-protector-all -fno-omit-frame-pointer -ggdb -Wno-error" CXXFLAGS="-DFORTIFY_SOURCE=2 -fstack-protector-all -fno-omit-frame-pointer -ggdb -Wno-error"
build_command:make clean && make CC=crepair-cc CXX=crepair-cxx CFLAGS="-ldl  -Wno-error -g" CXXFLAGS="-ldl  -Wno-error -g" LDFLAGS="-ldl  -Wno-error -g"
test_input_list:-w \$POC
poc_list:1
klee_flags:--link-llvm-lib=/CrashRepair/lib/libcrepair_proxy.bca
EOF
