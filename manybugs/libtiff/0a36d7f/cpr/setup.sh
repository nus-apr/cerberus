project_name=libtiff
bug_id=0a36d7f
dir_name=$1/manybugs/$project_name/$bug_id
current_dir=$PWD

cd $dir_name/src

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
make CXX=wllvm++ CC=wllvm CFLAGS="-L/CPR/lib -ltrident_proxy -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32
cd ./test
make clean
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-L/CPR/lib -ltrident_proxy -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32 long_tag.log
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
