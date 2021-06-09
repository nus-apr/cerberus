script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

cd $dir_name/src
make clean

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi


## Prepare for KLEE
# Fix fabs calls (not supported by KLEE).
sed -i 's/fabs/fabs_trident/g' libtiff/tif_luv.c
sed -i 's/fabs/fabs_trident/g' tools/tiff2ps.c
#sed -i 's/fabs_trident/fabs/g' libtiff/tif_luv.c
#sed -i 's/fabs_trident/fabs/g' tools/tiff2ps.c

make CC=$TRIDENT_CC CXX=$TRIDENT_CXX -j32

cd $dir_name

## Instrument test driver
sed -i '33i #include <klee/klee.h>' src/test/short_tag.c
sed -i '44i const char      *filename = "short_test.tiff";' src/test/short_tag.c
sed -i '45d' src/test/short_tag.c
sed -i '82i main(int argc, char **argv)'  src/test/short_tag.c
sed -i '83d' src/test/short_tag.c
sed -i '87i \\tfilename = argv[1];\n'  src/test/short_tag.c

## Instrument libtiff component.
sed -i '43i // KLEE' src/test/short_tag.c
sed -i '44i #include <klee/klee.h>' src/test/short_tag.c
sed -i '45i #ifndef TRIDENT_OUTPUT' src/test/short_tag.c
sed -i '46i #define TRIDENT_OUTPUT(id, typestr, value) value' src/test/short_tag.c
sed -i '47i #endif' src/test/short_tag.c

sed -i '187i \\t\t\tTRIDENT_OUTPUT("obs", "i32", check);' src/test/short_tag.c
sed -i '187i \\t\t\tint check = CheckShortField(tif, short_single_tags[i].tag, short_single_tags[i].value);' src/test/short_tag.c

sed -i '101i { TIFFTAG_NUMBEROFINKS, 1, 1, TIFF_SHORT, 0, __trident_choice("L976", "bool", (int[]){TIFF_SETGET_UNDEFINED, TIFF_SETGET_UINT16, TIFF_SETGET_C16_ASCII}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0)), TIFF_SETGET_UNDEFINED, FIELD_CUSTOM, 1, 0, "NumberOfInks", NULL },' src/libtiff/tif_dirinfo.c
sed -i '102d' src/libtiff/tif_dirinfo.c


cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32
cd ./test
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 short_tag.log
extract-bc short_tag


## Copy remaining files to run CPR.
cd $script_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp -rf components $dir_name
cp t1.smt2 $dir_name
