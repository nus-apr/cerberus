project_name=libtiff
bug_id=207c78a
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
#wget $download_url
cp $current_dir/libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar .
tar xf libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar
mv libtiff-bug-2006-02-23-b2ce5d8-207c78a src
rm libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar
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
cp $current_dir/tif_dirwrite.c ./libtiff/tif_dirwrite.c
make distclean
chown -R root $dir_name

# Compile libtiff.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
sed -i '978 s/./\t&/' test/Makefile
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

cd $dir_name

# fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/libtiff-bug-2006-02-23-b2ce5d8-207c78a#/data/manybugs/libtiff/207c78a#g" test.sh
sed -i "s#/data/manybugs/libtiff/207c78a/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd libtiff#cd src#g" test.sh

cd src

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
