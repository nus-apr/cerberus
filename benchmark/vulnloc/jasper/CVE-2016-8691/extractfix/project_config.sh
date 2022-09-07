#!/bin/bash
compile_type=$1

current_dir=`pwd`

cd project

#####
autoreconf -i

# create build diretory and config
rm -rf klee
mkdir klee
cd klee

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=integer-divide-by-zero -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler CFLAGS="$cflags" ../configure --disable-debug --disable-dmalloc --disable-libjpeg --disable-opengl --enable-static --disable-shared

sed -i 's/inline//g' ../src/libjasper/base/jas_malloc.c
cp ./src/libjasper/include/jasper/jas_config.h ../src/libjasper/include/jasper/

cd ../..


