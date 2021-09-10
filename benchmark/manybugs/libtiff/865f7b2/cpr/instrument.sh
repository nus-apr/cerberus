#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$fix_id
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
sed -i '33i // KLEE' src/libtiff/tif_dirwrite.c
sed -i '34i #include <klee/klee.h>' src/libtiff/tif_dirwrite.c
sed -i '35i #ifndef TRIDENT_OUTPUT' src/libtiff/tif_dirwrite.c
sed -i '36i #define TRIDENT_OUTPUT(id, typestr, value) value' src/libtiff/tif_dirwrite.c
sed -i '37i #endif' src/libtiff/tif_dirwrite.c
#
sed -i '351i \\tif (__trident_choice("978", "bool", (int[]){tif->tif_rawcc, orig_rawcc}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)' src/libtiff/tif_dirwrite.c
sed -i '352d' src/libtiff/tif_dirwrite.c
#
sed -i '359i \\tklee_print_expr("tif->tif_rawcc=", tif->tif_rawcc);' src/libtiff/tif_dirwrite.c
sed -i '360i \\tTRIDENT_OUTPUT("obs", "i32", tif->tif_rawcc);' src/libtiff/tif_dirwrite.c
sed -i '361i \\tklee_assert(tif->tif_rawcc == 0);' src/libtiff/tif_dirwrite.c

## Compile instrumentation and test driver.
cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32
extract-bc tools/tiffcp
cd ./test
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 long_tag.log short_tag.log ascii_tag.log strip_rw.log



# Convert shell to binary as a driver
cd $dir_name/src/test
sed -i "s/IMG_UNCOMPRESSED/1/g" tiffcp-split.sh
sed -i "s/IMG_UNCOMPRESSED/1/g" tiffcp-split-join.sh
CC=$TRIDENT_CC CXX=$TRIDENT_CXX shc -f tiffcp-split.sh
CC=$TRIDENT_CC CXX=$TRIDENT_CXX shc -f tiffcp-split-join.sh
mv tiffcp-split.sh.x tiffcp-split
mv tiffcp-split-join.sh.x tiffcp-split-join

cat <<EOF > $dir_name/cpr/repair.conf
project_path:/experiment/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/constant_a.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2
depth:3
loc_patch:/experiment/$benchmark_name/$project_name/$fix_id/src/libtiff/tif_dirwrite.c:351
loc_bug:/experiment/$benchmark_name/$project_name/$fix_id/src/libtiff/tif_dirwrite.c:360
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
declare -a arr_const=("constant_a")
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
for i in "${arr_const[@]}"
do
cp /CPR/components/$i.smt2 $dir_name/cpr/components
done


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

