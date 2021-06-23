script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

cd $dir_name/src
make clean
make CC="cilly --save-temps -std=c99 -fno-optimize-sibling-calls -fno-strict-aliasing -fno-asm" -j`nproc`

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
