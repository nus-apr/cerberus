#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/experiments/$benchmark_name/$project_name/$fix_id
mkdir $dir_name/cpr
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

#Instrument driver and libtiff
sed -i '43i // KLEE' src/libtiff/tif_dirread.c
sed -i '44i #include <klee/klee.h>' src/libtiff/tif_dirread.c
#
sed -i '976i \\tif (!dir->tdir_count || !w || __trident_choice("L976", "bool", (int[]){(tsize_t)dir->tdir_count, w, cc}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0))' src/libtiff/tif_dirread.c
sed -i '977d' src/libtiff/tif_dirread.c
#

## Instrument Short_TAG
sed -i '43d ' src/test/short_tag.c
sed -i '43i const char      *filename = "short_test.tiff";' src/test/short_tag.c
sed -i '81i main(int argc, char** argv)' src/test/short_tag.c
sed -i '82d' src/test/short_tag.c
sed -i '89,150 s/^/\/\//' src/test/short_tag.c
sed -i '151i \\tfilename = argv[1];'  src/test/short_tag.c

## Instrument Strip_RW
sed -i '60i \\tfilename = argv[1];'  src/test/strip_rw.c
sed -i '76,82 s/^/\/\//' src/test/strip_rw.c
sed -i '118,124 s/^/\/\//' src/test/strip_rw.c
sed -i '135,141 s/^/\/\//' src/test/strip_rw.c
sed -i '90d'  src/test/strip_rw.c
sed -i '106d'  src/test/strip_rw.c
sed -i '132d'  src/test/strip_rw.c

## Instrument LongTag
sed -i '65,120 s/^/\/\//' src/test/long_tag.c
sed -i '122i \\tfilename = argv[1];'  src/test/long_tag.c


sed -i '54i // KLEE' src/libtiff/tif_unix.c
sed -i '55i #include <klee/klee.h>' src/libtiff/tif_unix.c
sed -i '56i #ifndef TRIDENT_OUTPUT' src/libtiff/tif_unix.c
sed -i '57i #define TRIDENT_OUTPUT(id, typestr, value) value' src/libtiff/tif_unix.c
sed -i '58i #endif' src/libtiff/tif_unix.c
sed -i '166i {' src/libtiff/tif_unix.c
sed -i '167i \\t tif = ((TIFF *)0);' src/libtiff/tif_unix.c
sed -i '168i \\t goto obs;' src/libtiff/tif_unix.c
sed -i '170i }' src/libtiff/tif_unix.c
sed -i '184i \\t tif = ((TIFF *)0);' src/libtiff/tif_unix.c
sed -i '185i \\t goto obs;' src/libtiff/tif_unix.c
sed -i '192i obs: TRIDENT_OUTPUT("obs", "i32", tif);' src/libtiff/tif_unix.c
sed -i '193i \\tklee_assert(tif > 0);' src/libtiff/tif_unix.c


# Compile instrumentation and test driver.
cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC  CFLAGS="-L/CPR/lib -ltrident_proxy -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32
cd ./test
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-L/CPR/lib -ltrident_proxy -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32 long_tag.log short_tag.log ascii_tag.log strip_rw.log
extract-bc long_tag


# Convert shell to binary as a driver
cd $dir_name/src/test
sed -i "s/IMG_UNCOMPRESSED/1/g" tiffcp-split.sh
sed -i "s/IMG_UNCOMPRESSED/1/g" tiffcp-split-join.sh
CC=$TRIDENT_CC CXX=$TRIDENT_CXX shc -f tiffcp-split.sh
CC=$TRIDENT_CC CXX=$TRIDENT_CXX shc -f tiffcp-split-join.sh
mv tiffcp-split.sh.x tiffcp-split
mv tiffcp-split-join.sh.x tiffcp-split-join


cat <<EOF > $dir_name/cpr/repair.conf
project_path:$1/experiments/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/z.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2,division.smt2
depth:3
loc_patch:$1/experiments/$benchmark_name/$project_name/$fix_id/src/libtiff/tif_dirread.c:976
loc_bug:$1/experiments/$benchmark_name/$project_name/$fix_id/src/libtiff/tif_unix.c:192
gen_limit:80
stack_size:15000
dist_metric:angelic
spec_path:cpr/spec.smt2
test_input_dir:cpr/test-input-files
test_output_dir:cpr/test-expected-output
seed_dir:cpr/seed-dir
path_seed_suite:cpr/seed-config.json
path_test_suite:cpr/test-config.json
EOF


# Create patch components
mkdir $dir_name/cpr/components
declare -a arr_var=("x" "y" "z")
#declare -a arr_const=("constant_a")
# Create components for program variables
for i in "${arr_var[@]}"
do
cat <<EOF > $dir_name/cpr/components/$i.smt2
(declare-const rvalue_$i (_ BitVec 32))
(declare-const lvalue_$i (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(declare-const lreturn (_ BitVec 32))
(assert (and (= rreturn rvalue_$i) (= lreturn lvalue_$i)))
EOF
done

# Create components for constants
#for i in "${arr_const[@]}"
#do
#cp /CPR/components/$i.smt2 $dir_name/cpr/components
#done


# Copy Seed Files
cd $dir_name/src/test
mkdir $dir_name/cpr/seed-dir
find . -type f -iname '*.tiff' -exec cp  {} $dir_name/cpr/seed-dir/ \;
find . -type f -iname '*.bmp' -exec cp  {} $dir_name/cpr/seed-dir/ \;
find . -type f -iname '*.gif' -exec cp  {} $dir_name/cpr/seed-dir/ \;
find . -type f -iname '*.pgm' -exec cp  {} $dir_name/cpr/seed-dir/ \;
find . -type f -iname '*.ppm' -exec cp  {} $dir_name/cpr/seed-dir/ \;
find . -type f -iname '*.pbm' -exec cp  {} $dir_name/cpr/seed-dir/ \;

# Copy remaining files to run CPR.
cp $script_dir/spec.smt2 $dir_name/cpr
cp -rf $script_dir/test-input-files $dir_name/cpr
cp -rf $script_dir/test-expected-output $dir_name/cpr
cp $script_dir/test-config.json $dir_name/cpr
cp $script_dir/seed-config.json $dir_name/cpr
