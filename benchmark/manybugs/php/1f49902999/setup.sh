#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/experiments/$benchmark_name/$project_name/$fix_id
scenario_id=php-bug-2011-02-01-01745fa657-1f49902999
diff_file=main/streams/userspace.c-01745fa657a9b3f8a8f79520a87c265ec3725792
bug_id=$(echo $scenario_id | rev | cut -d "-" -f 2 | rev)
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/${scenario_id}.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xf ${scenario_id}.tar.gz
mv ${scenario_id} src
rm ${scenario_id}.tar.gz
mv src/* .
rm -rf src

rm -rf  coverage* \
        configuration-oracle \
        local-root \
        limit* \
        php-tests-* \
        *.cache \
        *.debug.* \
        *~ \
        php.tar.gz && \
    mv test.sh test.sh.orig && \
    mv bug-failures bug-info && \
    cp bugged-program.txt manifest.txt && \
    mv *.lines bug-info && \
    mv fix-failures bug-info

chown -R root $dir_name
grep -o -P '(?<=")[^"]+.phpt(?=")' php-run-tests.c > tests.all.txt
grep -o -P '\d+(?= &&)' test.sh.orig > tests.indices.txt

mv $project_name src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
cd $dir_name/src
make distclean &> /dev/null
cp /experiments/benchmark/$benchmark_name/$project_name/base/* $dir_name
# apply libxml fix
cat ../libxml.patch | patch -p0

#./configure CFLAGS="-save-temps=obj"
#make -j`nproc`

#make distclean
./configure && make -j`nproc`


cd $dir_name
chmod +x tester.py test.sh

./tester.py build







