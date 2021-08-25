#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
scenario_id=gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1
diff_file=gzip.c-a1d3d4019d
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
        *.cache \
        *.debug.* \
        sanity \
        *~ \
        reconfigure \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv $project_name src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
sed -i "s#_GL_WARN_ON_USE (gets,#//#g" lib/stdio.in.h
sed -i "s#root/mountpoint-genprog/genprog-many-bugs/${scenario_id}/gzip#/data/manybugs/${project_name}/${fix_id}/src#g" tests/Makefile
sed -i "s#\$abs_srcdir#/data/manybugs/${project_name}/${fix_id}/src/tests#g" tests/hufts
chown -R root $dir_name

cd $dir_name
## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#/data/manybugs/${project_name}/${fix_id}#g" test.sh
sed -i "s#/data/manybugs/${project_name}/${fix_id}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd ${project_name}#cd src#g" test.sh

#sed -i "29d" test.sh
sed -i "6d" gzip-run-tests.pl
sed -i "s#run_test 2 #run_test 3 #g" test.sh
sed -i "s#run_test 1 #run_test 2 #g" test.sh
sed -i "27d" test.sh
sed -i "s#run_test 7 #run_test 6 #g" test.sh

# add fix instrumentation
sed -i '652iifd =ifd;' $dir_name/src/gzip.c
