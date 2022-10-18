#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
echo "libtiff/tif_ojpeg.i" > $dir_name/manifest.txt

chmod +w ~/.opam/4.12.0/lib/perl5/App/Cilly.pm
sed -i "2215s/S+/S*/"  ~/.opam/4.12.0/lib/perl5/App/Cilly.pm

apt-get update && apt-get install -y -q --no-install-recommends  libjpeg-dev liblzma-dev libz-dev
export PATH=/root/.opam/4.12.0/bin/:$PATH

cd $dir_name/src

sed -i "33s/1/0/" libtiff/tif_config.h

make clean
make --ignore-errors CC="cilly -D _Float128=double --merge --keepmerged --save-temps -std=c99 -fno-optimize-sibling-calls -fno-strict-aliasing -fno-asm" -j`nproc`

cp $script_dir/compile.pl $dir_name/src
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


cat <<EOF > $dir_name/test.sh
TEST_ID=\$1
pattern=\`expr substr "\$TEST_ID" 1 1\`
num=\`expr substr "\$TEST_ID" 2 \${#TEST_ID}\`
$script_dir/../test.sh /experiment \$num
EOF
chmod +x $dir_name/test.sh

cat <<EOF > $dir_name/src/repair.conf
--allow-coverage-fail
--no-rep-cache
--no-test-cache
--label-repair
--sanity no
--multi-file true
--search ww
--compiler-command perl compile.pl __EXE_NAME__ > build.log
--test-command timeout -k 50s 50s __TEST_SCRIPT__ __TEST_NAME__  > test.log 2>&1
--crossover subset
--rep cilpatch
--describe-machine
--program bugged-program.txt
--prefix preprocessed
--seed 0
--popsize 40
--generations 10
--promut 1
--fitness-in-parallel 1
--rep-cache default.cache
--continue
--minimization
EOF


