#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$fix_id

cd $dir_name/src
make clean
make CC="cilly --save-temps -std=c99 -fno-optimize-sibling-calls -fno-strict-aliasing -fno-asm" -j`nproc`

cp $dir_name/manifest.txt $dir_name/src/bugged-program.txt
cfile=$(head -n 1 $dir_name/manifest.txt)
cilfile=$(echo $(echo $cfile | cut -d$"." -f1).cil.c)

rm -rf preprocessed
mkdir -p `dirname preprocessed/$cfile`
cp $cilfile preprocessed/$cfile
cp preprocessed/$cfile $cfile
rm -rf coverage
rm -rf coverage.path.*
rm -rf repair.cache
rm -rf repair.debug.*

cp $script_dir/compile.sh $dir_name/src/compile.pl
chmod +x $dir_name/src/compile.pl
cd $dir_name/src
make clean

cat <<EOF > $dir_name/src/repair.conf
--allow-coverage-fail
--no-rep-cache
--no-test-cache
--label-repair
--sanity no
--multi-file
--search ww
--compiler-command perl compile.pl __EXE_NAME__ > build.log
--test-command timeout -k 50s 50s __TEST_SCRIPT__ __TEST_NAME__  > test.log 2>&1
--crossover subset
--rep cilpatch
--suffix-extension .c
--describe-machine
--program bugged-program.txt
--prefix preprocessed
--seed 0
--popsize 40
--generations 10
--promut 1
--mutp 0
--fitness-in-parallel 1
--rep-cache default.cache
--continue
EOF

