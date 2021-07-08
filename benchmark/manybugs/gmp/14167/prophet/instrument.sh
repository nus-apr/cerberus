script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

# Fix build script of Prophet
sed -i '79d' /prophet-gpl/tools/gmp-build.py
sed -i '79i \\tret = subprocess.call(["make", "CFLAGS=\\"-static\\""], env = my_env);'  /prophet-gpl/tools/gmp-build.py

