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


# Compile gzip.
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0'
CC=wllvm CXX=wllvm++ make CFLAGS="-g -O0 -static" -j32


cd $dir_name/src

## Instrument driver and libtiff
sed -i '73i // KLEE' gzip.c
sed -i '74i #include <klee/klee.h>' gzip.c
sed -i '75i #ifndef TRIDENT_OUTPUT' gzip.c
sed -i '76i #define TRIDENT_OUTPUT(id, typestr, value) value' gzip.c
sed -i '77i #endif' gzip.c
#
sed -i '658i \\t\tklee_print_expr("(before) ifd=", ifd);' gzip.c
sed -i '659i \\t\tifd = __trident_choice("659", "i32", (int[]){ifd, part_nb, to_stdout}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0);' gzip.c
sed -i '660i \\t\tklee_print_expr("obs=", ifd);' gzip.c
sed -i '661i \\t\tTRIDENT_OUTPUT("obs", "i32", ifd);' gzip.c
sed -i '662i \\t\tklee_assert(ifd == 0);' gzip.c

# Compile instrumentation and test driver.
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32



cat <<EOF > $dir_name/cpr/repair.conf
project_path:/experiment/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/z.smt2,cpr/components/constant_a.smt2
general_comp_list:addition.smt2,minus.smt2,multiplication.smt2,subtraction.smt2,division.smt2
depth:2
loc_patch:/experiment/$benchmark_name/$project_name/$fix_id/src/gzip.c:659
loc_bug:/experiment/$benchmark_name/$project_name/$fix_id/src/gzip.c:661
gen_limit:80
stack_size:15000
dist_metric:angelic
spec_path:cpr/spec.smt2
test_input_dir:cpr/test-input-files
test_output_dir:cpr/test-expected-output
seed_dir:cpr/seed-dir
path_seed_suite:cpr/seed-config.json
path_test_suite:cpr/test-config.json
mask_arg:0,1,2,3,4,5,6,7,8
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
mkdir $dir_name/cpr/seed-dir
cp $script_dir/../seed-dir/* $dir_name/cpr/seed-dir

# Copy remaining files to run CPR.
cp $script_dir/spec.smt2 $dir_name/cpr
cp -rf $script_dir/test-input-files $dir_name/cpr
cp -rf $script_dir/test-expected-output $dir_name/cpr
cp $script_dir/test-config.json $dir_name/cpr
cp $script_dir/seed-config.json $dir_name/cpr

