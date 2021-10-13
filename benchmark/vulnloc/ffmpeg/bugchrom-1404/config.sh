#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

CC=clang
CXX=clang++
cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -Wno-everything"

CFLAGS="$cflags"
CXXFLAGS="$cflags"
ENABLE_UBSAN=""
FFMPEG_DEPS_PATH=/ffmpeg_deps/libs

PKG_CONFIG_PATH="$FFMPEG_DEPS_PATH/lib/pkgconfig" CFLAGS="-I$FFMPEG_DEPS_PATH/include $CFLAGS" ./configure \
    --cc=$CC --cxx=$CXX --ld="$CXX $CXXFLAGS -std=c++11" \
    --extra-ldflags="-L$FFMPEG_DEPS_PATH/lib $ENABLE_UBSAN" \
    --extra-cflags="$ENABLE_UBSAN" \
    --extra-cxxflags="$ENABLE_UBSAN" \
    --prefix="$FFMPEG_DEPS_PATH" \
    --pkg-config-flags="--static" \
    --enable-ossfuzz \
    --libfuzzer=$LIB_FUZZING_ENGINE \
    --optflags= \
    --enable-gpl \
    --enable-libass \
    --enable-libfdk-aac \
    --enable-libfreetype \
    --enable-libmp3lame \
    --enable-libopus \
    --enable-libtheora \
    --enable-libvorbis \
    --enable-libvpx \
    --enable-nonfree \
    --disable-muxers \
    --disable-protocols \
    --disable-devices \
    --disable-shared \
    --enable-cross-compile \
    --arch=x86_64 \
    --target-os=linux
