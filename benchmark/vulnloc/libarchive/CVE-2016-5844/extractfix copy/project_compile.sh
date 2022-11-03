#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
PROJECT_CFLAGS="-lm"
clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..
