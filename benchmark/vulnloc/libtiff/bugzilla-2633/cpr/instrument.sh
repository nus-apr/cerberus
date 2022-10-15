#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
mkdir $dir_name/cpr
cd $dir_name/src
make clean



./autogen.sh
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
CC=wllvm CXX=wllvm++ make -j32

sed -i 's/fabs/fabs_cpr/g' libtiff/tif_luv.c
sed -i 's/fabs/fabs_cpr/g' tools/tiff2ps.c
git add  libtiff/tif_luv.c tools/tiff2ps.c
git commit -m 'replace fabs with proxy function'

sed -i '118d;221d' libtiff/tif_jpeg.c
sed -i '153d;2463d' libtiff/tif_ojpeg.c
git add libtiff/tif_ojpeg.c libtiff/tif_jpeg.c
git commit -m 'remove longjmp calls'


make CFLAGS="-lcpr_proxy -L/CPR/lib" -j32

sed -i '2470i CPR_OUTPUT("obs", "i32", es);' tools/tiff2ps.c
sed -i '2441i if(__cpr_choice("L1634", "bool", (int[]){es, breaklen}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) return;' tools/tiff2ps.c
sed -i '44i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif\n' tools/tiff2ps.c
git add tools/tiff2ps.c
git commit -m "instrument cpr"




cat <<EOF > $dir_name/cpr/repair.conf
project_path:$dir_name
tag_id:$bug_id
src_directory:src
config_command:skip
build_command:make -j32
depth:3
test_output_list:cpr/t1.smt2
spec_path:cpr/spec.smt2
binary_path:tools/tiff2ps
custom_comp_list:components/x.smt2,components/y.smt2
general_comp_list:equal.smt2,not-equal.smt2,less-than.smt2,less-or-equal.smt2,constant_a.smt2
test_input_list:\$POC
poc_path:$script_dir/../tests/1.tif
static:true
loc_patch:$dir_name/src/tools/tiff2ps.c:2445
loc_bug:$dir_name/src/tools/tiff2ps.c:2475
klee_flags:--link-llvm-lib=/CPR/lib/libcpr_proxy.bca
gen_limit:40
stack_size:15000

EOF


# Create patch components
mkdir $dir_name/cpr/components
declare -a arr_var=("x" "y")
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
