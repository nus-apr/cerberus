#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
KLEE_CFLAGS="-L${current_dir}/project_specific_lib/"
PROJECT_CFALGS="-"
clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..
