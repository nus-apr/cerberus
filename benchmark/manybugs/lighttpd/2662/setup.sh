project_name=lighttpd
bug_id=2662
scenario_id=lighttpd-bug-2661-2662
diff_file=src/mod_accesslog.c-2661
dir_name=$1/manybugs/$project_name/$bug_id
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
        compile.pl \
        *~ \
        test \
        reconfigure \
        preprocessed \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv libtiff src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
make distclean
chown -R root $dir_name


cd $dir_name

# fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/lighttpd-bug-2661-2662#/data/manybugs/lighttpd/2662/#g" test.sh
sed -i "s#/data/manybugs/lighttpd/2662/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i 's#lt-\.\*#lt-\.\* \&\> /dev/null#g' test.sh
sed -i 's#cd lighttpd/tests#pushd /data/manybugs/lighttpd/2662/src/tests#g' test.sh
sed -i 's#cd ../../#popd#g' test.sh

# fix an obnoxious bug in tests/core-request.t
sed -i 's#image.JPG#image.jpg#g' src/tests/core-request.t

# fix broken symlinks
cd src/tests/tmp/lighttpd/servers/www.example.org/pages
rm symlinked index.xhtml
ln -s expire symlinked
ln -s index.html index.xhtml

# fix broken test file
cp $current_dir/mod-cgi.t /data/manybugs/lighttpd/1914/src/tests/mod-cgi.t

# compile program
cd $dir_name/src
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --with-pcre=yes --with-ldap --with-bzip2 --with-openssl --with-gdbm --with-memcache --with-webdav-props --with-webdav-locks
#CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared --with-pcre=yes --with-ldap --with-bzip2 --with-openssl --with-gdbm --with-memcache --with-webdav-props --with-webdav-locks
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32
