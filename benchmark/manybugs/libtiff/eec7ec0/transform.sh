#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


SRC_FILE=$dir_name/src/tools/tiff2pdf.c
TRANS_FILE=$script_dir/valkyrie/tiff2pdf.c
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
cp -rf $dir_name/src/test $script_dir/test-suite


cd $dir_name/src
driver_list=($(find -type f -executable -exec file -i '{}' \; | grep 'charset=binary' | grep -v "shellscript" | awk '{print $1}'))
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

script_list=($(find -type f -executable -exec file -i '{}' \; |grep  "shellscript" | grep "\.sh" | awk '{print $1}'))
for i in "${script_list[@]}"
do
  script_path=${i::-1}
  sed -i "s#o-#\$PATCH_ID-o-#g" $script_path
done


sed -i 's#main()#main(int argc, char **argv)#g' $dir_name/src/test/long_tag.c
sed -i 's#main()#main(int argc, char **argv)#g' $dir_name/src/test/short_tag.c
sed -i 's#static const char filename\[\]#const char \*filename#g' $dir_name/src/test/short_tag.c
sed -i "67 i if (argc > 1) filename = argv[1] + '-' + *filename; " $dir_name/src/test/long_tag.c
sed -i "86 i if (argc > 1) filename = argv[1] + '-' + *filename; " $dir_name/src/test/short_tag.c
sed -i "62 i if (argc > 1) filename = argv[1] + '-' + *filename; " $dir_name/src/test/strip_rw.c

cd $script_dir
bash build.sh $1

