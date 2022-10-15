#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/cpr
cd $dir_name/src
make clean


sed -i '292i klee_assert(i > size / 2 );\n' src/shred.c
sed -i '292i CPR_OUTPUT("obs", "i32", i - (size/2));\n' src/shred.c
sed -i '290d' src/shred.c
sed -i '290i for(i = 3; (__cpr_choice("L290", "bool", (int[]){size, i}, (char*[]){"size","i"}, 2, (int*[]){}, (char*[]){}, 0)); i *= 2)' src/shred.c
sed -i '97i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif' src/shred.c
sed -i '97i #include <klee/klee.h>' src/shred.c
git add src/shred.c
git commit -m "instrument cpr"

./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$CPR_CC CXX=$CPR_CXX ./configure CFLAGS='-g -O0 -static -fPIE' CXXFLAGS="$CFLAGS"
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS -j32
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS src/shred -j32



cat <<EOF > $dir_name/cpr/repair.conf
project_path:$dir_name
tag_id:$bug_id
src_directory:src
config_command:skip
build_command:skip
depth:3
test_output_list:cpr/t1.smt2
spec_path:cpr/spec.smt2
binary_path:src/shred
custom_comp_list:cpr/components/i.smt2,cpr/components/size.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2,division.smt2,constant_a.smt2
test_input_list:-n 4 -s 7 \$POC
poc_path:$script_dir/../tests/1.txt
static:false
build_flags:disable
loc_patch:$dir_name/src/src/shred.c:290
loc_bug:$dir_name/src/src/shred.c:292
dist_metric:angelic
max-fork:100
mask_arg:0,2,4
EOF


# Create patch components
mkdir $dir_name/cpr/components
declare -a arr_var=("i" "size")
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
(assert (= true (bvsgt obs!0 (_ bv0 32) )))
EOF

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi
