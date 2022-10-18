#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$fix_id
scenario_id=libtiff-bug-2006-03-03-a72cf60-0a36d7f
diff_file=libtiff/tif_dirread.c-a72cf60
bug_id=$(echo $scenario_id | rev | cut -d "-" -f 2 | rev)
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/${scenario_id}.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url --no-check-certificate
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
        compile.pl \
        *~ \
        test \
        reconfigure \
        preprocessed \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv $project_name src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
chown -R root $dir_name

make distclean
git checkout $(cat ../manifest.txt)


cd $dir_name
## fix the test harness and the profile script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#${dir_name}#g" test.sh
sed -i "s#${dir_name}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd ${project_name}#cd src#g" test.sh