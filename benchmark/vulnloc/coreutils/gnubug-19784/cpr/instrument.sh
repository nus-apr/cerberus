#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/cpr
cd $dir_name/src
make clean


autoreconf -i
CC=wllvm CXX=wllvm++ ./configure --enable-static --disable-shared CFLAGS='-g -O0 -static -ftrapv' CXXFLAGS="$CFLAGS"
sed -i '1234i CPR_OUTPUT("obs", "i32", dec->yend - dec->tileyoff);\n' src/libjasper/jpc/jpc_dec.c
sed -i '1229i if(__cpr_choice("L1229", "bool", (int[]){dec->yend, dec->tileyoff, INT_MAX}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0)) return -1;' src/libjasper/jpc/jpc_dec.c
sed -i '90i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif\n' src/libjasper/jpc/jpc_dec.c
git add src/libjasper/jpc/jpc_dec.c
git commit -m "instrument cpr"
make CC=$CPR_CC CXX=$CPR_CXX  CFLAGS='-g -O0 -static -ftrapv' CXXFLAGS="$CFLAGS" -j32



cat <<EOF > $dir_name/cpr/repair.conf
project_path:$dir_name
tag_id:$bug_id
src_directory:src
binary_path:src/make-prime-list
config_command:skip
build_command:skip
spec_path:cpr/spec.smt2
custom_comp_list:cpr/components/i.smt2,cpr/components/size.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,addition.smt2,constant_a.smt2
test_input_list:15
test_output_list:cpr/t1.smt2
depth:3
static:false
build_flags:disable
loc_patch:$dir_name/src/src/make-prime-list.c:214
loc_bug:$dir_name/src/src/make-prime-list.c:215
dist_metric:angelic
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
(assert (= true (bvsge (concat  (select  output!i32!obs!0 (_ bv3 32) ) (concat  (select  output!i32!obs!0 (_ bv2 32) ) (concat  (select  output!i32!obs!0 (_ bv1 32) ) (select  output!i32!obs!0 (_ bv0 32) ) ) ) ) (_ bv1 32)) ))

EOF

cat <<EOF > $dir_name/cpr/t1.smt2
(declare-const obs!0 (_ BitVec 32))
(assert (= true (bvsge obs!0 (_ bv1 32) )))

EOF

if [ ! -f "$dir_name/src/INSTRUMENTED_CPR" ]; then
    touch "$dir_name/src/INSTRUMENTED_CPR"
fi
