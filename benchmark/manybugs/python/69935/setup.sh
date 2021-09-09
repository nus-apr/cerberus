#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/experiments/$benchmark_name/$project_name/$fix_id
scenario_id=python-bug-69934-69935
diff_file=Modules/signalmodule.c-69934
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
mv $project_name src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
chown -R root $dir_name


cd $dir_name
## fix the test harness and the configuration script
sed -i "s/cd python/cd src/" test.sh
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#$1/experiments/manybugs/${project_name}/${fix_id}#g" test.sh
sed -i "s#$1/experiments/manybugs/${project_name}/${fix_id}/limit#timeout 300#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd ${project_name}#cd src#g" test.sh
sed -i "s#&> /dev/null##" python-run-tests.pl

# disable 'test_create_connection' in 'test_socket'
sed -i "s#def test_create_connection_timeout(self):#def test_create_connection(self):\n        return#" src/Lib/test/test_socket.py



