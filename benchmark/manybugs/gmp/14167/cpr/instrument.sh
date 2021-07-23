script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
mkdir $dir_name/cpr


cd $dir_name/src
make clean

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi


# Compile gmp.
CC=wllvm CXX=wllvm++ ./configure --disable-shared --enable-static --disable-fft --disable-mpbsd --disable-cxx --disable-fast-install --disable-minithres
CC=wllvm CXX=wllvm++ ./configure --disable-shared --disable-cxx --disable-fast-install --enable-static;

cd $dir_name/src

sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
make -e fib_table.h;make -e mp_bases.h;
CC=clang CXX=clang++ make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32


cp ../diffs/mpn/generic/powm.c-13420 mpn/generic/powm.c
sed -i '76i #include <klee/klee.h>' mpn/generic/powm.c
sed -i '213d' mpn/generic/powm.c
sed -i '213i b2p = ( __trident_choice("L1634", "i32", (int[]){rp, tp, n}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0));' mpn/generic/powm.c
sed -i '228i klee_silent_exit(0);' mpn/generic/powm.c

sed -i '23i #include <klee/klee.h>' mpn/generic/add_n.c
sed -i '23i #endif' mpn/generic/add_n.c
sed -i '23i #define TRIDENT_OUTPUT(id, typestr, value) value' mpn/generic/add_n.c
sed -i '23i #ifndef TRIDENT_OUTPUT' mpn/generic/add_n.c
sed -i '45i klee_assert(vp - rp == 1 || up - rp == 1);' mpn/generic/add_n.c
sed -i '45i TRIDENT_OUTPUT("obs", "i32", vp - rp == 1 || up - rp == 1);' mpn/generic/add_n.c

# instrument driver for input generation
sed -i "111d" tests/mpz/t-gcd.c
sed -i "111i int reps = atoi(argv[1]); " tests/mpz/t-gcd.c
sed -i "111i char* filename = argv[2];" tests/mpz/t-gcd.c
sed -i "139i char line1 [1000];\n char line2 [1000];" tests/mpz/t-gcd.c
sed -i "141i FILE *file = fopen ( filename, "r" );" tests/mpz/t-gcd.c
sed -i "142i if (file != NULL) { fgets(line1,sizeof line1,file);  fgets(line2,sizeof line2,file); fclose(file);  }" tests/mpz/t-gcd.c
sed -i "143i else {    perror(filename); }" tests/mpz/t-gcd.c
sed -i "145,149d" tests/mpz/t-gcd.c
sed -i "145i mpz_set_str (op1, line1, 16);\n mpz_set_str (op2, line2, 16);" tests/mpz/t-gcd.c


sed -i 's/wllvm++/\/CPR\/tools\/trident-cxx/g' mpn/Makefile
sed -i 's/wllvm/\/CPR\/tools\/trident-cc/g' mpn/Makefile
CC=$TRIDENT_CC CXX=$TRIDENT_CXX make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32
cd tests/mpz
sed -i 's/wllvm++/\/CPR\/tools\/trident-cxx/g' Makefile
sed -i 's/wllvm/\/CPR\/tools\/trident-cc/g' Makefile
CC=$TRIDENT_CC CXX=$TRIDENT_CXX make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" t-gcd



cat <<EOF > $dir_name/cpr/repair.conf
project_path:/data/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/z.smt2,cpr/components/constant_a.smt2
general_comp_list:addition.smt2
depth:3
loc_patch:/data/$benchmark_name/$project_name/$fix_id/src/mpn/generic/powm.c:213
loc_bug:/data/$benchmark_name/$project_name/$fix_id/src/mpn/generic/add_n.c:45
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
mkdir $dir_name/cpr/seed-dir
cp $script_dir/../seed-dir/* $dir_name/cpr/seed-dir

# Copy remaining files to run CPR.
cp $script_dir/spec.smt2 $dir_name/cpr
cp -rf $script_dir/test-input-files $dir_name/cpr
cp -rf $script_dir/test-expected-output $dir_name/cpr
cp $script_dir/test-config.json $dir_name/cpr
cp $script_dir/seed-config.json $dir_name/cpr

