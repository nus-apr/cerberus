script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
scenario_id=gmp-bug-14166-14167
diff_file=mpz/gcdext.c-14166
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

cd $dir_name/src

mkdir tests/mpbsd/
touch tests/mpbsd/Makefile.in
rm $dir_name/src/ltmain.sh
cp $script_dir/ltmain.sh ltmain.sh
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' configure.in
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile.am

cd $dir_name
## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#/data/manybugs/${project_name}/${fix_id}#g" test.sh
sed -i "s#/data/manybugs/${project_name}/${fix_id}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd ${project_name}#cd src#g" test.sh
sed -i 's#lt-\.\*#lt-\.\* \&\> /dev/null#g' test.sh
sed -i '190d' gmp-run-tests.pl
sed -i '190i my $cmd = sprintf("k=%s && rm -f \\$k && make \\$k && ./\\$k", $name);' gmp-run-tests.pl
chmod +x gmp-run-tests.pl


