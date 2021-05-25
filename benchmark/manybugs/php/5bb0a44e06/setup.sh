project_name=php
bug_id=5bb0a44e06
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/php-bug-2011-02-05-c50b3d7add-426f31e790.tar.gz
current_dir=$PWD
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
mv $project_name src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
make distclean
chown -R root $dir_name





cd src/php

make clean
CC=wllvm CXX=wllvm++  ./configure \
  --enable-cli \
  --disable-dom \
  --disable-libxml  \
  --disable-xml \
  --disable-simplexml \
  --disable-xmlreader  \
  --disable-xmlwriter  \
  --disable-pear  \
  --disable-phar \
  --disable-inline-optimization  \
  --without-pcre-dir  \
  --disable-fileinfo \
  --disable-shared

CC=clang CXX=clang++ make  -j32

sed -i 's/fabs/fabs_trident/g' ./ext/gd/libgd/gd.c
sed -i 's/fabs/fabs_trident/g' ./ext/gd/libgd/gd_rotate.c
sed -i 's/fabs/fabs_trident/g' ./ext/sqlite3/libsqlite/sqlite3.c
sed -i 's/fabs/fabs_trident/g' ./ext/standard/math.c

make CXX=clang++ CC=clang LDFLAGS="-ltrident_proxy -L/CPR/lib -L/klee/build/lib -lkleeRuntest" CFLAGS="-g -O0 -static"  sapi/cli/php
