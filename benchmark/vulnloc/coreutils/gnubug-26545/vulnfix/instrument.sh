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
sed -i '1215i #include "/home/yuntong/vulnfix/thirdparty/AFL/experimental/argv_fuzzing/argv-fuzz-inl.h"' src/shred.c
sed -i "1220i AFL_INIT_SET03(\"./shred\", \"$dummy_file\");" src/shred.c
# -u option can cause a lot of files to be writting to disk during fuzzing; disable that
sed -i '1260i break;' src/shred.c
# remove and recreate output so that it does not grow too big.
sed -i '1320i FILE* file_ptr = fopen(file[i], "w"); fclose(file_ptr);' src/shred.c
# not bulding man pages
sed -i '217d' Makefile.am

./bootstrap
export FORCE_UNSAFE_CONFIGURE=1 && ./configure
make CFLAGS="-Wno-error -fsanitize=address -ggdb" CXXFLAGS="-Wno-error -fsanitize=address -ggdb" LDFLAGS="-fsanitize=address" -j`nproc`

config_path=$dir_name/vulnfix/config

cat > $config_path <<EOL
cmd=
fix-location=shred.c:290
crash-location=shred.c:293
input-from-stdin=true
fix-file-path=src/shred.c
fix-line=290
build-cmd=make clean && make CFLAGS="-Wno-error -fsanitize=address -ggdb" CXXFLAGS="-Wno-error -fsanitize=address -ggdb" LDFLAGS="-fsanitize=address" -j10
EOL
