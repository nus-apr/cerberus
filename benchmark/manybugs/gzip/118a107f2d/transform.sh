#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id


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
sed -i 's#/experiment//manybugs/gzip/118a107f2d/src/tests#/tmp#g' test-suite/tests/hufts


