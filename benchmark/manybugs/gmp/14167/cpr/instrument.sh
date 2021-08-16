#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
mkdir $dir_name/cpr
diff_file=mpz/gcdext.c-14166
cd $dir_name/src
make clean

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi


cd $dir_name/src

sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
make -e fib_table.h;make -e mp_bases.h;
make CC=wllvm CXX=wllvm++  CFLAGS="-g -O0 -static -std=c99 -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32

sed -i '25i #endif' mpz/gcdext.c
sed -i '25i #define TRIDENT_OUTPUT(id, typestr, value) value' mpz/gcdext.c
sed -i '25i #ifndef TRIDENT_OUTPUT' mpz/gcdext.c
sed -i '25i #include <klee/klee.h>' mpz/gcdext.c
sed -i '25i // KLEE' mpz/gcdext.c
sed -i '60i if (__trident_choice("L1634", "bool", (int[]){siz, bsize, asize}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0)) ssize = 0;' mpz/gcdext.c
sed -i '61i TRIDENT_OUTPUT("obs", "i32", ssize - (asize!=0));' mpz/gcdext.c


# instrument driver for input generation
cp /experiments/benchmark/manybugs/gmp/.aux/testcase/t-gcd-cpr.c $dir_name/src/tests/mpz/t-gcd.c

sed -i 's/wllvm++/\/CPR\/tools\/trident-cxx/g' mpn/Makefile
sed -i 's/wllvm/\/CPR\/tools\/trident-cc/g' mpn/Makefile
make CC=$TRIDENT_CC CXX=$TRIDENT_CXX  CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32
cd tests/mpz
sed -i 's/wllvm++/\/CPR\/tools\/trident-cxx/g' Makefile
sed -i 's/wllvm/\/CPR\/tools\/trident-cc/g' Makefile
make CC=$TRIDENT_CC CXX=$TRIDENT_CXX CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" t-gcd


cat <<EOF > $dir_name/cpr/repair.conf
project_path:/data/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/z.smt2,cpr/components/constant_a.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2
depth:3
loc_patch:/data/$benchmark_name/$project_name/$fix_id/src/mpz/gcdext.c:60
loc_bug:/data/$benchmark_name/$project_name/$fix_id/src/mpz/gcdext.c:61
gen_limit:80
stack_size:15000
dist_metric:angelic
spec_path:cpr/spec.smt2
test_input_dir:cpr/test-input-files
test_output_dir:cpr/test-expected-output
seed_dir:cpr/seed-dir
path_seed_suite:cpr/seed-config.json
path_test_suite:cpr/test-config.json
klee_flags:-no-exit-on-error
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

