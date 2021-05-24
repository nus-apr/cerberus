project_name=libtiff
bug_id=7d6e298
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