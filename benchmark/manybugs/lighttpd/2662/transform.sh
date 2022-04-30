#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id



SRC_FILE=$dir_name/src/src/mod_accesslog.c
TRANS_FILE=$script_dir/valkyrie/mod_accesslog.c
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

# copy test cases
cp -rf $dir_name/src/tests $script_dir/test-suite/
find $script_dir/test-suite -type d -exec chmod 775 {} \;

# copy libraries
cp -rf $dir_name/src/src/.libs $script_dir/test-suite/src
cp -rf $dir_name/src/src/*.la $script_dir/test-suite/src


cd $dir_name/src
driver_list=($(find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'  | grep -v ".so" ))
for i in "${driver_list[@]}"
do
  driver_path=${i::-1}
  directories=$(dirname $driver_path)
  driver_name=$(basename $driver_path)
  mkdir -p $script_dir/test-suite/$directories
  cp $script_dir/test-suite/template $script_dir/test-suite/$directories/$driver_name
  cp $driver_path $script_dir/test-suite/$directories/$driver_name.orig
  sed -i "s#TEMP#$driver_name#g" $script_dir/test-suite/$directories/$driver_name
done



