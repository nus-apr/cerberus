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

## Instrument test driver (TIFFTAG_DOTRANGE=336)
sed -i '33i #include <klee/klee.h>' src/test/short_tag.c
sed -i '70,79 s/^/\/\//' src/test/short_tag.c
sed -i '80i #define NPAIREDTAGS   4' src/test/short_tag.c
sed -i '83i main(int argc, char** argv)' src/test/short_tag.c
sed -i '84d' src/test/short_tag.c

sed -i '124i \\n'  src/test/short_tag.c
sed -i '125i \\tuint32 symDotRangeTag;'  src/test/short_tag.c
sed -i '127i \\tsymDotRangeTag = atoi(argv[1]);'  src/test/short_tag.c
sed -i '129i \\n'  src/test/short_tag.c

sed -i '130i \\tconst struct {'  src/test/short_tag.c
sed -i '131i \\t\tconst ttag_t    tag;'  src/test/short_tag.c
sed -i '132i \\t\tconst uint16    values[2];'  src/test/short_tag.c
sed -i '133i \\t} short_paired_tags[] = {'  src/test/short_tag.c
sed -i '134i \\t\t{ TIFFTAG_PAGENUMBER, {1, 1} },'  src/test/short_tag.c
sed -i '135i \\t\t{ TIFFTAG_HALFTONEHINTS, {0, 255} },'  src/test/short_tag.c
sed -i '136i \\t\t{ symDotRangeTag, {8, 16} },'  src/test/short_tag.c
#sed -i '143i \\t\t{ symDotRangeTag, {symLowBound, symHighBound} },'  src/test/short_tag.c
sed -i '137i \\t\t//    { TIFFTAG_DOTRANGE, {8, 16} }, //, {8, 16} }, // uint32 ttag_t TIFFTAG_DOTRANGE'  src/test/short_tag.c
sed -i '138i \\t\t{ TIFFTAG_YCBCRSUBSAMPLING, {2, 1} }'  src/test/short_tag.c
sed -i '139i \\t};'  src/test/short_tag.c

## Instrument libtiff component.
sed -i '33i // KLEE' src/libtiff/tif_dirwrite.c
sed -i '34i #include <klee/klee.h>' src/libtiff/tif_dirwrite.c
sed -i '35i #ifndef TRIDENT_OUTPUT' src/libtiff/tif_dirwrite.c
sed -i '36i #define TRIDENT_OUTPUT(id, typestr, value) value' src/libtiff/tif_dirwrite.c
sed -i '37i #endif' src/libtiff/tif_dirwrite.c

sed -i '810i \\t\t\tklee_print_expr("val=",v[0]);' src/libtiff/tif_dirwrite.c
sed -i '811i \\t\t\tTRIDENT_OUTPUT("obs", "i32", v[0]);' src/libtiff/tif_dirwrite.c

sed -i '343i \\t\t\tif(__trident_choice("L1634", "bool", (int[]){fip->field_tag, TIFFTAG_DOTRANGE}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) {' src/libtiff/tif_dirwrite.c
sed -i '344i \\t\t\t\tgoto bad;' src/libtiff/tif_dirwrite.c
sed -i '345i \\t\t\t} else if (!TIFFWriteNormalTag(tif, dir, fip))' src/libtiff/tif_dirwrite.c
sed -i '346d' src/libtiff/tif_dirwrite.c

cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32
cd ./test
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 short_tag.log
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 long_tag.log
extract-bc short_tag
extract-bc long_tag

## Copy remaining files to run CPR.
cd $script_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp -rf components $dir_name
cp t1.smt2 $dir_name
