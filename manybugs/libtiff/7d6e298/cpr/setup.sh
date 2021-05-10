project_name=libtiff
bug_id=7d6e298
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2007-07-19-ce4b7af-7d6e298.tar
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
#wget $download_url
cp $current_dir/libtiff-bug-2007-07-19-ce4b7af-7d6e298.tar .
tar xf libtiff-bug-2007-07-19-ce4b7af-7d6e298.tar
mv libtiff-bug-2007-07-19-ce4b7af-7d6e298 src
rm libtiff-bug-2007-07-19-ce4b7af-7d6e298.tar
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
cp $current_dir/tif_dirinfo.c ./libtiff/tif_dirinfo.c
make distclean
chown -R root $dir_name

## Compile libtiff.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
sed -i '978 s/./\t&/' test/Makefile
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

cd $dir_name

## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/libtiff-bug-2007-07-19-ce4b7af-7d6e298#/data/manybugs/libtiff/7d6e298#g" test.sh
sed -i "s#/data/manybugs/libtiff/7d6e298/src/limit#timeout 5#g" test.sh
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
sed -i '34i // KLEE' src/libtiff/tif_dirinfo.c
sed -i '35i #include <klee/klee.h>' src/libtiff/tif_dirinfo.c
sed -i '36i #ifndef TRIDENT_OUTPUT' src/libtiff/tif_dirinfo.c
sed -i '37i #define TRIDENT_OUTPUT(id, typestr, value) value' src/libtiff/tif_dirinfo.c
sed -i '38i #endif' src/libtiff/tif_dirinfo.c
#
sed -i '294i \\t\ttif->tif_fields = __trident_choice("294", "i32", (int[]){tif->tif_fields, NULL, tif->tif_nfields}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0);' src/libtiff/tif_dirinfo.c
sed -i '295d' src/libtiff/tif_dirinfo.c
#
sed -i '297i \\tint tmp_obs = _TIFFMergeFields(tif, fieldarray->fields, fieldarray->count);' src/libtiff/tif_dirinfo.c
sed -i '298i \\tklee_print_expr("obs=", tmp_obs);' src/libtiff/tif_dirinfo.c
sed -i '299i \\tTRIDENT_OUTPUT("obs", "i32", tmp_obs);' src/libtiff/tif_dirinfo.c
sed -i '300i \\tklee_assert(tmp_obs != 0);' src/libtiff/tif_dirinfo.c
sed -i '301i \\tif(!tmp_obs) {' src/libtiff/tif_dirinfo.c
sed -i '302d' src/libtiff/tif_dirinfo.c

## Compile instrumentation and test driver.
cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32
cd tools
extract-bc tiffcp

## Copy remaining files to run CPR.
cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp test-input $dir_name
cp -rf components $dir_name
cp -rf test-input-files $dir_name
cp -rf test-expected-output $dir_name
#cp -rf seed-dir $dir_name

#### Test with KLEE
#cd /data/manybugs/libtiff/865f7b2/src/tools
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/test-input-files/22-44-54-64-74-fail-palette-1c-1b.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/test-input-files/13-14-15-16-17-22-43-53-63-73-fail-miniswhite-1c-1b.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/seed-dir/2-pass-long_test.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/seed-dir/22-40-50-60-70-pass-minisblack-1c-16b.tiff test.tif
##
#cd /data/manybugs/libtiff/865f7b2/test-input-files
#gen-bout --sym-file "/data/manybugs/libtiff/865f7b2/test-input-files/22-44-54-64-74-fail-palette-1c-1b.tiff"
#cd /data/manybugs/libtiff/865f7b2/src/tools
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/libtiff/865f7b2/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching tiffcp.bc A --sym-files 1 3312 test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/libtiff/865f7b2/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching tiffcp.bc A --sym-files 1 3312 test.tif
##
