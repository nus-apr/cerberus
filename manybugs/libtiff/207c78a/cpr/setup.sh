project_name=libtiff
bug_id=207c78a
dir_name=$1/manybugs/$project_name/$bug_id

current_dir=$PWD

cd $dir_name/src

### Prepare for KLEE
## Fix fabs calls (not supported by KLEE).
#sed -i 's/fabs/fabs_trident/g' libtiff/tif_luv.c
#sed -i 's/fabs/fabs_trident/g' tools/tiff2ps.c
##sed -i 's/fabs_trident/fabs/g' libtiff/tif_luv.c
##sed -i 's/fabs_trident/fabs/g' tools/tiff2ps.c
#
#make CC=$TRIDENT_CC CXX=$TRIDENT_CXX -j32
#
#cd $dir_name
#
### Instrument test driver (TIFFTAG_DOTRANGE=336)
#sed -i '33i #include <klee/klee.h>' src/test/short_tag.c
#sed -i '70,79 s/^/\/\//' src/test/short_tag.c
#sed -i '80i #define NPAIREDTAGS   4' src/test/short_tag.c
#sed -i '83i main(int argc, char** argv)' src/test/short_tag.c
#sed -i '84d' src/test/short_tag.c
#
#sed -i '124i \\n'  src/test/short_tag.c
#sed -i '125i \\tuint32 symDotRangeTag;'  src/test/short_tag.c
##sed -i '126i \\tklee_make_symbolic(&symDotRangeTag, sizeof(symDotRangeTag), "symDotRangeTag");'  src/test/short_tag.c
##sed -i '127i \\t//symDotRangeTag = TIFFTAG_DOTRANGE;'  src/test/short_tag.c
#sed -i '127i \\tsymDotRangeTag = atoi(argv[1]);'  src/test/short_tag.c
##sed -i '128i \\tklee_print_expr("symVal=", symDotRangeTag);'  src/test/short_tag.c
#sed -i '129i \\n'  src/test/short_tag.c
##sed -i '130i \\tint symLowBound, symHighBound;'  src/test/short_tag.c
##sed -i '131i \\tklee_make_symbolic(&symLowBound, sizeof(symLowBound), "symLowBound");'  src/test/short_tag.c
##sed -i '132i \\tklee_make_symbolic(&symHighBound, sizeof(symHighBound), "symHighBound");'  src/test/short_tag.c
##sed -i '133i \\t//symLowBound = 8;'  src/test/short_tag.c
##sed -i '134i \\t//symHighBound = 16;'  src/test/short_tag.c
##sed -i '135i \\tklee_print_expr("symLowBound=", symLowBound+symHighBound);'  src/test/short_tag.c
##sed -i '136i \\n'  src/test/short_tag.c
#sed -i '130i \\tconst struct {'  src/test/short_tag.c
#sed -i '131i \\t\tconst ttag_t    tag;'  src/test/short_tag.c
#sed -i '132i \\t\tconst uint16    values[2];'  src/test/short_tag.c
#sed -i '133i \\t} short_paired_tags[] = {'  src/test/short_tag.c
#sed -i '134i \\t\t{ TIFFTAG_PAGENUMBER, {1, 1} },'  src/test/short_tag.c
#sed -i '135i \\t\t{ TIFFTAG_HALFTONEHINTS, {0, 255} },'  src/test/short_tag.c
#sed -i '136i \\t\t{ symDotRangeTag, {8, 16} },'  src/test/short_tag.c
##sed -i '143i \\t\t{ symDotRangeTag, {symLowBound, symHighBound} },'  src/test/short_tag.c
#sed -i '137i \\t\t//    { TIFFTAG_DOTRANGE, {8, 16} }, //, {8, 16} }, // uint32 ttag_t TIFFTAG_DOTRANGE'  src/test/short_tag.c
#sed -i '138i \\t\t{ TIFFTAG_YCBCRSUBSAMPLING, {2, 1} }'  src/test/short_tag.c
#sed -i '139i \\t};'  src/test/short_tag.c
#
### Instrument libtiff component.
#sed -i '33i // KLEE' src/libtiff/tif_dirwrite.c
#sed -i '34i #include <klee/klee.h>' src/libtiff/tif_dirwrite.c
#sed -i '35i #ifndef TRIDENT_OUTPUT' src/libtiff/tif_dirwrite.c
#sed -i '36i #define TRIDENT_OUTPUT(id, typestr, value) value' src/libtiff/tif_dirwrite.c
#sed -i '37i #endif' src/libtiff/tif_dirwrite.c
#
#sed -i '810i \\t\t\tklee_print_expr("val=",v[0]);' src/libtiff/tif_dirwrite.c
#sed -i '811i \\t\t\tTRIDENT_OUTPUT("obs", "i32", v[0]);' src/libtiff/tif_dirwrite.c
#
#sed -i '343i \\t\t\tif(__trident_choice("L1634", "bool", (int[]){fip->field_tag, TIFFTAG_DOTRANGE}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) {' src/libtiff/tif_dirwrite.c
#sed -i '344i \\t\t\t\tgoto bad;' src/libtiff/tif_dirwrite.c
#sed -i '345i \\t\t\t} else if (!TIFFWriteNormalTag(tif, dir, fip))' src/libtiff/tif_dirwrite.c
#sed -i '346d' src/libtiff/tif_dirwrite.c
#
#cd src
#make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32
#cd ./test
#make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 short_tag.log
#make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 long_tag.log
#extract-bc short_tag
#extract-bc long_tag
##klee --posix-runtime --libc=uclibc -link-llvm-lib=/concolic-repair/lib/libtrident_runtime.bca -write-smt2s short_tag.bc
#
#cd $current_dir
#cp repair.conf $dir_name
#cp spec.smt2 $dir_name
#cp t1.smt2 $dir_name
#cp -rf components $dir_name
#
#
#
#
#
##test
##%
#
##CC=wllvm CXX=wllvm++ ./configure CFLAGS='-m32' CXXFLAGS='-m32' LDFLAGS='-m32' --enable-static --disable-shared
##CC=wllvm CXX=wllvm++ make -j32
#
#
##sudo apt-get update
##sudo apt-get install -y --force-yes psmisc
##sudo apt-get install -y --force-yes zlib1g-dev
##sudo apt-get install -y --force-yes gcc-multilib
##sudo apt-get install -y --force-yes g++-multilib
##    sudo apt-get clean && \
##    sudo apt-get autoremove && \
##    sudo rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*
#
#
#
#
#
#
##sed -i '118d;221d' libtiff/tif_jpeg.c
##sed -i '153d;2429d' libtiff/tif_ojpeg.c
##git add libtiff/tif_ojpeg.c libtiff/tif_jpeg.c
##git commit -m 'remove longjmp calls'
#
#
##make CFLAGS="-ltrident_proxy -L/concolic-repair/lib -g" -j32
##sed -i '358i }' tools/gif2tiff.c
##sed -i '353i { TRIDENT_OUTPUT("obs", "i32", count);\n if (count < 0) klee_abort();\n' tools/gif2tiff.c
##sed -i '352d' tools/gif2tiff.c
##sed -i '352i while ((count = getc(infile)) &&  count <= 255 && (__trident_choice("L65", "bool", (int[]){count, status}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) )' tools/gif2tiff.c
##sed -i '43i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif\n' tools/gif2tiff.c
##git add tools/gif2tiff.c
##git commit -m "instrument trident"
#
##cd $current_dir
##cp repair.conf $dir_name
##cp spec.smt2 $dir_name
##cp t1.smt2 $dir_name
##cp -rf components $dir_name
##cp -rf tests $dir_name
#
