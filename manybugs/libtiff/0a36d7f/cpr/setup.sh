project_name=libtiff
bug_id=0a36d7f
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2006-03-03-a72cf60-0a36d7f.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
#wget $download_url
cp $current_dir/libtiff-bug-2006-03-03-a72cf60-0a36d7f.tar.gz .
tar xfz libtiff-bug-2006-03-03-a72cf60-0a36d7f.tar.gz
mv libtiff-bug-2006-03-03-a72cf60-0a36d7f src
rm libtiff-bug-2006-03-03-a72cf60-0a36d7f.tar.gz
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
cp $current_dir/tif_dirread.c ./libtiff/tif_dirread.c
make distclean
chown -R root $dir_name

# Compile libtiff.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
sed -i '978 s/./\t&/' test/Makefile
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

cd $dir_name

# fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/libtiff-bug-2006-03-03-a72cf60-0a36d7f#/data/manybugs/libtiff/0a36d7f#g" test.sh
sed -i "s#/data/manybugs/libtiff/0a36d7f/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd libtiff#cd src#g" test.sh

cd src

## Prepare for KLEE
# Fix fabs calls (not supported by KLEE).
sed -i 's/fabs/fabs_trident/g' libtiff/tif_luv.c
sed -i 's/fabs/fabs_trident/g' tools/tiff2ps.c
#sed -i 's/fabs_trident/fabs/g' libtiff/tif_luv.c
#sed -i 's/fabs_trident/fabs/g' tools/tiff2ps.c

make CC=$TRIDENT_CC CXX=$TRIDENT_CXX -j32

cd $dir_name

#Instrument driver and libtiff
sed -i '43i // KLEE' src/libtiff/tif_dirread.c
sed -i '44i #include <klee/klee.h>' src/libtiff/tif_dirread.c
#
sed -i '976i \\tif (!dir->tdir_count || !w || __trident_choice("L976", "bool", (int[]){(tsize_t)dir->tdir_count, w, cc}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0))' src/libtiff/tif_dirread.c
sed -i '977d' src/libtiff/tif_dirread.c
#
sed -i '35i // KLEE' src/test/long_tag.c
sed -i '36i #include <klee/klee.h>' src/test/long_tag.c
sed -i '37i #ifndef TRIDENT_OUTPUT' src/test/long_tag.c
sed -i '38i #define TRIDENT_OUTPUT(id, typestr, value) value' src/test/long_tag.c
sed -i '39i #endif' src/test/long_tag.c
##
sed -i '69i \\tfilename = argv[1];'  src/test/long_tag.c
sed -i '70,125 s/^/\/\//' src/test/long_tag.c
sed -i '129i \\tklee_print_expr("tif=", tif);' src/test/long_tag.c
sed -i '130i \\tTRIDENT_OUTPUT("obs", "i32", tif);' src/test/long_tag.c
sed -i '131i \\tklee_assert(tif > 0);' src/test/long_tag.c


# Compile instrumentation and test driver.
cd src
make CXX=wllvm++ CC=wllvm CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32
cd ./test
make clean
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32 long_tag.log
extract-bc long_tag

# Copy remaining files to run CPR.
cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp test-input $dir_name
cp seed-file $dir_name
cp -rf components $dir_name
cp -rf test-input-files $dir_name
cp -rf test-expected-output $dir_name
cp -rf seed-dir $dir_name

cd $dir_name
#cp test-input-files/long_test.tiff src/test/
#cd src/test/
#gen-bout --sym-file "/data/manybugs/libtiff/0a36d7f/src/test/long_test.tiff"

#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s long_tag.bc long_test.tiff
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s --seed-out=file.bout --allow-seed-extension --named-seed-matching long_tag.bc A --sym-files 1 156
