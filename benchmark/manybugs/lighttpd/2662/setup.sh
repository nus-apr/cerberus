#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=$1/$benchmark_name/$project_name/$fix_id
scenario_id=lighttpd-bug-2661-2662
diff_file=src/mod_accesslog.c-2661
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
chown -R root $dir_name


# Prophet requires/works on git source
cd $dir_name
svn checkout -r $bug_id svn://svn.lighttpd.net/lighttpd/branches/lighttpd-1.4.x src-svn

cd $dir_name

## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#/experiment/manybugs/${project_name}/${fix_id}#g" test.sh
sed -i "s#/experiment/manybugs/${project_name}/${fix_id}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i 's#lt-\.\*#lt-\.\* \&\> /dev/null#g' test.sh
sed -i "s#cd ${project_name}#pushd ${dir_name}/src#g" test.sh
sed -i 's#cd ../../#popd#g' test.sh
sed -i "42d" test.sh

# add instrumentation for fix
sed -i '168d' src/src/mod_accesslog.c
sed -i '168i if (0 == 1) return;' src/src/mod_accesslog.c


sed -i "s#run_test 20 #run_test 21 #g" test.sh
sed -i "s#run_test 18 #run_test 20 #g" test.sh
sed -i "s#run_test 17 #run_test 18 #g" test.sh
sed -i "s#run_test 16 #run_test 17 #g" test.sh
sed -i "s#run_test 15 #run_test 16 #g" test.sh
sed -i "s#run_test 14 #run_test 15 #g" test.sh
sed -i "s#run_test 13 #run_test 14 #g" test.sh
sed -i "s#run_test 12 #run_test 13 #g" test.sh
sed -i "s#run_test 9 #run_test 12 #g" test.sh


# fix an obnoxious bug in tests/core-request.t
sed -i 's#image.JPG#image.jpg#g' src/tests/core-request.t
sed -i '49,71 s/^/#/' src/tests/mod-cgi.t

# fix broken symlinks
cd src/tests/tmp/lighttpd/servers/www.example.org/pages
rm symlinked index.xhtml
ln -s expire symlinked
ln -s index.html index.xhtml

cd $dir_name
# fix test-case-id
cp src/tests/core-condition.t src/tests/1.t
cp src/tests/mod-rewrite.t src/tests/2.t
cp src/tests/lowercase.t src/tests/3.t
cp src/tests/mod-redirect.t src/tests/4.t
cp src/tests/mod-secdownload.t src/tests/5.t
cp src/tests/mod-ssi.t src/tests/6.t
cp src/tests/core-var-include.t src/tests/7.t
cp src/tests/core-keepalive.t src/tests/8.t
cp src/tests/mod-cgi.t src/tests/9.t
cp src/tests/core.t src/tests/10.t
cp src/tests/core-request.t src/tests/11.t
cp src/tests/mod-access.t src/tests/12.t
cp src/tests/mod-compress.t src/tests/13.t
cp src/tests/mod-setenv.t src/tests/14.t
cp src/tests/fastcgi.t src/tests/15.t
cp src/tests/cachable.t src/tests/16.t
cp src/tests/mod-userdir.t src/tests/17.t
cp src/tests/core-response.t src/tests/18.t
cp src/tests/request.t src/tests/19.t
cp src/tests/mod-auth.t src/tests/20.t
cp src/tests/symlink.t src/tests/21.t
