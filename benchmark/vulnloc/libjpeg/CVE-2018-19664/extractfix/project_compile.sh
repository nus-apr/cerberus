#!/bin/bash
source=$1
target=$2

current_dir=`pwd`
cd project
KLEE_CFLAGS="-L${current_dir}/project_specific_lib/"
PROJECT_CFLAGS="-llzma -lz -lm -ljpeg -ljbig -lhook ${current_dir}/project/klee/libjpeg.a -ljpeg ${current_dir}/project/klee/libturbojpeg.a -lturbojpeg"
clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..
