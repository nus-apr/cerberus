#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$fix_id

# Fix build script of Prophet
sed -i '79d' /prophet-gpl/tools/gmp-build.py
sed -i '79i \\tret = subprocess.call(["make", "CFLAGS=\\"-static\\""], env = my_env);'  /prophet-gpl/tools/gmp-build.py

cp $dir_name/src/gmp.h $dir_name/src/mpz/
cp $dir_name/src/gmp-impl.h $dir_name/src/mpz/
mkdir $dir_name/prophet

mkdir $dir_name/patches
cat <<EOF > $dir_name/prophet/prophet.conf
revision_file=/experiment/$benchmark_name/$project_name/$fix_id/prophet/prophet.revlog
src_dir=/experiment/$benchmark_name/$project_name/$fix_id/src
test_dir=/experiment/$benchmark_name/$project_name/$fix_id/src/tests
bugged_file=mpz/gcdext.c
fixed_out_file=patches/$project_name-fix-$fix_id.c
build_cmd=/prophet-gpl/tools/$project_name-build.py
test_cmd=/prophet-gpl/tools/$project_name-test.py
localizer=profile
single_case_timeout=120
wrap_ld=yes
EOF

cat <<EOF > $dir_name/prophet/prophet.revlog
-
-
Diff Cases: Tot 1
7
Positive Cases: Tot 4
8 2 3 6
Regression Cases: Tot 0

EOF