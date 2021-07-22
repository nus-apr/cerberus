script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

cd $dir_name/src
make clean

cp $dir_name/manifest.txt $dir_name/src/bugged-program.txt
cp -r $dir_name/preprocessed $dir_name/src/preprocessed

rm -rf coverage
rm -rf coverage.path.*
rm -rf repair.cache
rm -rf repair.debug.*

cp $script_dir/compile.sh $dir_name/src/compile.pl
chmod +x $dir_name/src/compile.pl
cd $dir_name/src
make clean