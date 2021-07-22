script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

cp -rf $dir_name/preprocessed $dir_name/src
cd $dir_name/src

rm -rf coverage
rm -rf coverage.path.*
rm -rf repair.cache
rm -rf repair.debug.*

cp $dir_name/compile.pl $dir_name/src
sed -i "s#project = \"php\"#project = "\"${dir_name}/src\""#g" $dir_name/src/compile.pl