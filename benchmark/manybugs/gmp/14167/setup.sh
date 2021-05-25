project_name=gmp
bug_id=14167
scenario_id=gmp-bug-14166-14167
diff_file=mpz/gcdext.c-14166
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


# Compile gzip.
make clean
mkdir tests/mpbsd/
touch tests/mpbsd/Makefile.in
cp $current_dir/ltmain.sh ltmain.sh
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' configure.in
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile.am
./.bootstrap
CC=wllvm CXX=wllvm++ ./configure --disable-shared --enable-static --disable-fft --disable-mpbsd --disable-cxx --disable-fast-install --disable-minithres

CC=wllvm CXX=wllvm++ ./configure --disable-shared --disable-cxx --disable-fast-install --enable-static;
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
make -e fib_table.h;make -e mp_bases.h;
CC=clang CXX=clang++ make -j32

