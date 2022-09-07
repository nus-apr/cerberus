#!/bin/bash
compile_type=$1

current_dir=`pwd`


cd project
#git checkout 8d34b45

# TODO: coreutils must run ./bootstrap once after checkout
#./bootstrap

#sed -i '214s/sieve\[++i\] == 0/\n({++i;\nsieve[i] == 0;})/' src/make-prime-list.c


# create build diretory and config
rm -rf klee
mkdir klee
cd klee

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/ -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-no-replace-globals -mllvm -lowfat-memcpy-overlap -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler FORCE_UNSAFE_CONFIGURE=1  ../configure --disable-nls CFLAGS="$cflags"

cd ../..

