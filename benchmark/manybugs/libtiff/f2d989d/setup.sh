project_name=libtiff
bug_id=e0b51f3
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2009-06-30-b44af47-e0b51f3.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xf libtiff-bug-2009-06-30-b44af47-e0b51f3.tar.gz
mv libtiff-bug-2009-06-30-b44af47-e0b51f3 src
rm libtiff-bug-2009-06-30-b44af47-e0b51f3.tar.gz
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
cp $dir_name/diffs/tools/tiffcp.c-b44af47 $dir_name/src/tools/tiffcp.c
make distclean
chown -R root $dir_name

# Compile libtiff.
make clean
./configure CFLAGS='-g -O0' --enable-static --disable-shared
sed -i '978 s/./\t&/' test/Makefile
make CFLAGS="-march=x86-64" -j32
cd $dir_name

