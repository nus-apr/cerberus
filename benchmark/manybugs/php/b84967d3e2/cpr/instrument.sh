#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$fix_id

mkdir $dir_name/cpr
cd $dir_name/src
make clean

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi

## Prepare for KLEE

if [ -e configured.mark ]; then
    echo "[php-transform] Already configured"

    # Makefile
    sed -i 's/all_targets = $(OVERALL_TARGET) $(PHP_MODULES) $(PHP_ZEND_EX) $(PHP_BINARIES) pharcmd/all_targets = $(OVERALL_TARGET) $(PHP_MODULES) $(PHP_ZEND_EX) $(PHP_BINARIES)/' ./Makefile
    sed -i 's/PHP_BINARIES = cli cgi/PHP_BINARIES = cli/' ./Makefile

    exit 0
fi

aux=$(readlink -f "/experiments/benchmark/manybugs/php/.aux")
main_c_appendix=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/main/main.c.appendix")
php_h_appendix=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/main/php.h.appendix")
test_univ=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/TEST_UNIV_FULL")
# extend main.c
cp $main_c_appendix ./main/
cat ./main/main.c ./main/main.c.appendix > ./main/main.c.merge
cp ./main/main.c ./main/main.c.bak
cp ./main/main.c.merge ./main/main.c
$aux/get_test_script_file.awk $test_univ >> ./main/main.c

# extend php.h
cp $php_h_appendix ./main/
cp ./main/php.h ./main/php.h.bak
cat ./main/php.h ./main/php.h.appendix > ./main/php.h.merge
cp ./main/php.h.merge ./main/php.h

#sed -i "21i #define FD_ZERO_SIMUL(set) memset(set, 0, sizeof(*(set)))" main/php.h

files=$(grep -rl "FD_ZERO(" --include=*.c) || true
for file in $files; do
    sed -i 's/FD_ZERO(/FD_ZERO_SIMUL(/g' $file
done

files=$(grep -rl "(char \*)gnu_get_libc_version()" --include=*.c) || true
for file in $files; do
    sed -i 's/(char \*)gnu_get_libc_version()/\"2.27\"/g' $file
done

files=$(grep -rl "# define XPFPA_HAVE_CW 1" --include=*.h) || true
for file in $files; do
    sed -i 's/# define XPFPA_HAVE_CW 1//g' $file
done

files=$(grep -rl "#define HAVE_MMAP 1" --include=*.h) || true
for file in $files; do
    sed -i 's/#define HAVE_MMAP 1//g' $file
done

# php_crypt_r.c
sed -i 's/#elif (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 2))/#elif defined(AF_KEEP_ORG) \&\& (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 2))/g' ./ext/standard/php_crypt_r.c
sed -i 's/#elif (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 1))/#elif defined(AF_KEEP_ORG) \&\& (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 1))/g' ./ext/standard/php_crypt_r.c
sed -i 's/#elif defined(HAVE_ATOMIC_H)/#elif defined(AF_KEEP_ORG) \&\& defined(HAVE_ATOMIC_H)/g' ./ext/standard/php_crypt_r.c

# zend_alloc.c
sed -i 's/#if defined(__GNUC__) && defined(i386)/#if defined(AF_KEEP_ORG) \&\& defined(__GNUC__) \&\& defined(i386)/g' ./Zend/zend_alloc.c
sed -i 's/#elif defined(__GNUC__) && defined(__x86_64__)/#elif defined(AF_KEEP_ORG) \&\& defined(__GNUC__) \&\& defined(__x86_64__)/g' ./Zend/zend_alloc.c
sed -i 's/#elif defined(_MSC_VER) && defined(_M_IX86)/#elif defined(AF_KEEP_ORG) \&\& defined(_MSC_VER) \&\& defined(_M_IX86)/g' ./Zend/zend_alloc.c

# zend.h
sed -i 's/# define EXPECTED(condition)   __builtin_expect(condition, 1)/# define EXPECTED(condition)   (__builtin_expect(condition, 1))/g' ./Zend/zend.h
sed -i 's/# define UNEXPECTED(condition) __builtin_expect(condition, 0)/# define UNEXPECTED(condition) (__builtin_expect(condition, 0))/g' ./Zend/zend.h


# Makefile
sed -i 's/all_targets = $(OVERALL_TARGET) $(PHP_MODULES) $(PHP_ZEND_EX) $(PHP_BINARIES) pharcmd/all_targets = $(OVERALL_TARGET) $(PHP_MODULES) $(PHP_ZEND_EX) $(PHP_BINARIES)/' ./Makefile
sed -i 's/PHP_BINARIES = cli cgi/PHP_BINARIES = cli/' ./Makefile

touch configured.mark


cd $dir_name/src
#Instrument for test-case
sed -i '20i // KLEE' Zend/zend_execute.c
sed -i '21i #include <klee/klee.h>' Zend/zend_execute.c
sed -i '22i #ifndef TRIDENT_OUTPUT' Zend/zend_execute.c
sed -i '23i #define TRIDENT_OUTPUT(id, typestr, value) value' Zend/zend_execute.c
sed -i '24i #endif' Zend/zend_execute.c
sed -i '1267i }' Zend/zend_execute.c
sed -i '1266i \\tklee_assert(type - BP_VAR_IS != 0);' Zend/zend_execute.c
sed -i '1266i \\tTRIDENT_OUTPUT("obs", "i32", type - BP_VAR_IS);' Zend/zend_execute.c
sed -i '1266i \\tif ( __trident_choice("L154", "bool", (int[]){type, BP_VAR_IS}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) {' Zend/zend_execute.c

# Compile instrumentation and test driver.
make CXX=wllvm++ CC=wllvm LDFLAGS="-L/CPR/lib -ltrident_runtime -L/klee/build/lib  -lkleeRuntest " EXTRA_CFLAGS="-g -I/klee/source/include -include /CPR/lib/trident_runtime.h" -j32


cd $dir_name/src/sapi/cli
extract-bc php
llvm-dis php.bc
line=$(grep -n "declare double @llvm.fabs.f64(double)" php.ll | cut -d ":" -f 1)
sed -i "$line d" php.ll
sed -i "$line i }" php.ll
sed -i "$line i ret double %11" php.ll
sed -i "$line i %11 = phi double [ %6, %5 ], [ %9, %7 ]" php.ll
sed -i "$line i ; <label>:10:                                      ; preds = %7, %5" php.ll
sed -i "$line i br label %10" php.ll
sed -i "$line i %9 = fsub double -0.000000e+00, %8"  php.ll
sed -i "$line i %8 = load double, double* %2, align 8" php.ll
sed -i "$line i ; <label>:7:                                      ; preds = %1" php.ll
sed -i "$line i br label %10" php.ll
sed -i "$line i %6 = load double, double* %2, align 8" php.ll
sed -i "$line i ; <label>:5:                                      ; preds = %1" php.ll
sed -i "$line i br i1 %4, label %5, label %7" php.ll
sed -i "$line i %4 = fcmp ogt double %3, 0.000000e+00" php.ll
sed -i "$line i %3 = load double, double* %2, align 8" php.ll
sed -i "$line i store double %0, double* %2, align 8" php.ll
sed -i "$line i %2 = alloca double, align 8" php.ll
sed -i "$line i define double @fabs_f64(double) #0 {" php.ll
sed -i 's#\@llvm.fabs.f64#\@fabs_f64#g' php.ll
llvm-as php.ll


cat <<EOF > $dir_name/cpr/repair.conf
project_path:/experiment/$benchmark_name/$project_name/$fix_id
tag_id:$fix_id
src_directory:src
config_command:skip
build_command:skip
binary_path:sapi/cli/php
custom_comp_list:cpr/components/x.smt2,cpr/components/y.smt2,cpr/components/constant_a.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2
depth:3
loc_patch:/experiment/$benchmark_name/$project_name/$fix_id/src/Zend/zend_execute.c:1266
loc_bug:/experiment/$benchmark_name/$project_name/$fix_id/src/Zend/zend_execute.c:1267
gen_limit:30
stack_size:15000
dist_metric:angelic
spec_path:cpr/spec.smt2
seed_file:cpr/seed-input
test_input_file:cpr/test-input
test_output_list:cpr/expected-output/t1.smt2
mask_arg:$(seq -s "," -f "%g" 0 53)
preserve_bc:true
max_flippings:25
timeout_concrete:300
timeout_concolic:1800
generalize_seed_input:-d output_handler= -d open_basedir= -d safe_mode=0 -d disable_functions= -d output_buffering=Off -d error_reporting=32767 -d display_errors=1 -d display_startup_errors=1 -d log_errors=0 -d html_errors=0 -d track_errors=1 -d report_memleaks=1 -d report_zend_debug=0 -d docref_root= -d docref_ext=.html -d error_prepend_string= -d error_append_string= -d auto_prepend_file= -d auto_append_file= -d magic_quotes_runtime=0 -d ignore_repeated_errors=0 -d precision=14 -d unicode.runtime_encoding=ISO-8859-1 -d unicode.script_encoding=UTF-8 -d unicode.output_encoding=UTF-8 -d unicode.from_error_mode=U_INVALID_SUBSTITUTE -f \$POC
generalize_test_input:-d output_handler= -d open_basedir= -d safe_mode=0 -d disable_functions= -d output_buffering=Off -d error_reporting=32767 -d display_errors=1 -d display_startup_errors=1 -d log_errors=0 -d html_errors=0 -d track_errors=1 -d report_memleaks=1 -d report_zend_debug=0 -d docref_root= -d docref_ext=.html -d error_prepend_string= -d error_append_string= -d auto_prepend_file= -d auto_append_file= -d magic_quotes_runtime=0 -d ignore_repeated_errors=0 -d precision=14 -d unicode.runtime_encoding=ISO-8859-1 -d unicode.script_encoding=UTF-8 -d unicode.output_encoding=UTF-8 -d unicode.from_error_mode=U_INVALID_SUBSTITUTE -f \$POC
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


# Create seed profile
echo " " > $dir_name/cpr/seed-input
while IFS= read -r line
do
  sed -i "1i \$POC_${line%.phpt}.php" $dir_name/cpr/seed-input
done < $dir_name/tests.all.txt.rev

# Create test profile
echo " " > $dir_name/cpr/test-input
while IFS= read -r line
do
  sed -i "1i \$POC_${line%.phpt}.php" $dir_name/cpr/test-input
done < $dir_name/failing.tests.txt


# Copy remaining files to run CPR.
cp $script_dir/spec.smt2 $dir_name/cpr
cp -rf $script_dir/expected-output $dir_name/cpr

