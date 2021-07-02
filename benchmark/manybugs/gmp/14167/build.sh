script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$bug_id
cd $dir_name/src


sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
# Compile gmp
make -e fib_table.h;make -e mp_bases.h;
make -e  CFLAGS="-march=x86-64 -g -O0 -static" -j`nproc`
