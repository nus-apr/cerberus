#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


SRC_FILE=$dir_name/src/Zend/zend_compile.c
TRANS_FILE=$script_dir/valkyrie/zend_compile.c
ANNOTATE_SCRIPT=$script_dir/../../../../scripts/transform/annotate.py
MERGE_SCRIPT=$script_dir/../../../../scripts/transform/merge.py

if [[ ! -f $TRANS_FILE ]]; then
  mkdir -p $(dirname $TRANS_FILE)
  clang-tidy $SRC_FILE -fix -checks="readability-braces-around-statements"
  clang-format -style=LLVM  $SRC_FILE > $TRANS_FILE
  cp $TRANS_FILE $SRC_FILE
  clang -Xclang -ast-dump=json $SRC_FILE > $TRANS_FILE.ast
  tr --delete '\n' <  $TRANS_FILE.ast  >  $TRANS_FILE.ast.single
  # check for multi-line if condition / for condition  / while condition
  python3 $MERGE_SCRIPT $TRANS_FILE $TRANS_FILE.ast.single
  mv merged.c $TRANS_FILE
  cp $TRANS_FILE $SRC_FILE
  clang -Xclang -ast-dump=json $SRC_FILE > $TRANS_FILE.ast.merged
  tr --delete '\n' <  $TRANS_FILE.ast.merged  >  $TRANS_FILE.ast.merged.single
  python3 $ANNOTATE_SCRIPT $TRANS_FILE $TRANS_FILE.ast.merged.single
  mv annotated.c $TRANS_FILE
fi

cp  $TRANS_FILE $SRC_FILE
bash build.sh $1


# copy test driver
cp $dir_name/tester.py $script_dir/test-suite
cp $dir_name/tests.all.txt $script_dir/test-suite
cp $dir_name/src/run-tests.php $script_dir/test-suite


cd $dir_name/src

# copy test cases
cd $dir_name/src
test_list=($(find -name "*.phpt"))
for t in "${test_list[@]}"
do
  directories=$(dirname $t)
  test_name=$(basename $t)
  mkdir -p $script_dir/test-suite/$directories
  cp $t $script_dir/test-suite/$directories
done

driver_list=("sapi/cli/php")
for i in "${driver_list[@]}"
do
  driver_path=$i
  directories=$(dirname $driver_path)
  driver_name=$(basename $driver_path)
  mkdir -p $script_dir/test-suite/$directories
  cp $script_dir/test-suite/template $script_dir/test-suite/$directories/$driver_name
  cp $driver_path $script_dir/test-suite/$directories/$driver_name.orig
  sed -i "s#TEMP#$driver_name#g" $script_dir/test-suite/$directories/$driver_name
done

find $script_dir/test-suite -type d -exec chmod 775 {} \;