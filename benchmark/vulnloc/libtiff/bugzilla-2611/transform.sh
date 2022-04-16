#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id

SRC_FILE=$dir_name/src/libtiff/tif_ojpeg.c
TRANS_FILE=$script_dir/valkyrie/tif_ojpeg.c
ANNOTATE_SCRIPT=$script_dir/../../../../scripts/annotate.py

if [[ ! -f $TRANS_FILE ]]; then
  mkdir -p $(dirname $TRANS_FILE)
  clang-tidy $SRC_FILE -fix -checks="readability-braces-around-statements"
  clang-format -style=LLVM  $SRC_FILE > $TRANS_FILE
  cp $TRANS_FILE $SRC_FILE
  clang -Xclang -ast-dump=json $SRC_FILE > $TRANS_FILE.ast
  tr --delete '\n' <  $TRANS_FILE.ast  >  $TRANS_FILE.ast.single
  # check for multi-line if condition / for condition  / while condition
  python3 $ANNOTATE_SCRIPT $TRANS_FILE $TRANS_FILE.ast.single
  mv formatted.c $TRANS_FILE
fi

cp  $TRANS_FILE $SRC_FILE
bash build.sh $1


