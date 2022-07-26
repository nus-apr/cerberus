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
binary_path:$dir_name/src/src/pr
config_command:FORCE_UNSAFE_CONFIGURE=1 CC=crepair-cc ./configure CFLAGS="-g -O0 -static -fPIE -Wno-error" CXXFLAGS="-g -O0 -static -fPIE -Wno-error"
build_command:make CC=crepair-cc CXX=crepair-cxx CFLAGS="-ggdb -fPIC -fPIE -g -O0 -Wno-error" CXXFLAGS="-ggdb -fPIC -fPIE -g -O0 -Wno-error" LDFLAGS="-static"
test_input_list:"-S\$(printf "\t\t\t")" a -m \$POC
poc_list:$script_dir/../tests/1.txt
klee_flags:--link-llvm-lib=/CrashRepair/lib/libcrepair_proxy.bca
EOF
