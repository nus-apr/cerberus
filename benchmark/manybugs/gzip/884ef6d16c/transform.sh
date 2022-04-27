#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


SRC_FILE=$dir_name/src/gzip.c
TRANS_FILE=$script_dir/valkyrie/gzip.c
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



#copy shell-scripts
cp $dir_name/src/zdiff test-suite
cp $dir_name/src/znew test-suite
cp $dir_name/src/zless test-suite
cp $dir_name/src/zmore test-suite
cp $dir_name/src/zfgrep test-suite
cp $dir_name/src/zgrep test-suite
cp $dir_name/src/zcat test-suite
cp $dir_name/src/zcmp test-suite


# copy binary executables
#find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'
cp -f $dir_name/src/gzip test-suite/gzip.orig

# copy test cases
cp -rf $dir_name/src/tests test-suite

# update path for test case
sed -i 's#/experiment//manybugs/gzip/$bug_id/src/tests#/tmp#g' test-suite/tests/hufts


