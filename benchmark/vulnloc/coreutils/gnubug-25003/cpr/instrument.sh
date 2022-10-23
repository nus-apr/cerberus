#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/cpr
cd $dir_name/src
make clean

sed -i '987i klee_assert(initial_read > start);' src/split.c
sed -i '987i CPR_OUTPUT("obs", "i32", initial_read - start);\n' src/split.c
sed -i '985d' src/split.c
sed -i '985i if(__cpr_choice("L290", "bool", (int[]){start, initial_read, bufsize}, (char*[]){"start","initial_read", "bufsize"}, 3, (int*[]){}, (char*[]){}, 0))' src/split.c
sed -i '97i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif' src/split.c
sed -i '97i #include <klee/klee.h>' src/split.c
git add src/split.c
git commit -m "instrument cpr"

./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$CPR_CC CXX=$CPR_CXX ./configure CFLAGS='-g -O0 -static -fPIE' CXXFLAGS="$CFLAGS"
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS -j32
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS src/split -j32



cat <<EOF > $dir_name/cpr/repair.conf
project_path:$dir_name
tag_id:$bug_id
src_directory:src
config_command:skip
build_command:skip
depth:3
test_output_list:cpr/t1.smt2
spec_path:cpr/spec.smt2
binary_path:src/split
test_input_list:-n 7/75 /dev/null
custom_comp_list:cpr/components/start.smt2,cpr/components/initial_read.smt2,cpr/components/bufsize.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2,constant_a.smt2
loc_patch:$dir_name/src/src/split.c:989
loc_bug:$dir_name/src/src/split.c:991
build_flags:disable
mask_arg:0,2
dist_metric:angelic
static:false
EOF


# Create patch components
mkdir $dir_name/cpr/components
declare -a arr_var=("start" "initial_read" "bufsize")
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


# Create Specification Files
cat <<EOF > $dir_name/cpr/spec.smt2
(declare-fun output!i32!obs!0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= false (bvsle (concat  (select  output!i32!obs!0 (_ bv3 32) ) (concat  (select  output!i32!obs!0 (_ bv2 32) ) (concat  (select  output!i32!obs!0 (_ bv1 32) ) (select  output!i32!obs!0 (_ bv0 32) ) ) ) ) (_ bv0 32)) ))

EOF

cat <<EOF > $dir_name/cpr/t1.smt2
(declare-const obs!0 (_ BitVec 32))
(assert (= false (bvsle obs!0 (_ bv0 32) )))
EOF

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi
