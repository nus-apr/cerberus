#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
src_dir_name=$dir_name/src
cd $src_dir_name


seed_dir=$script_dir/../seed-dir
# Copy Seed Files
mkdir $seed_dir
cp $script_dir/../tests/*  $seed_dir


cd $src_dir_name

if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi


cat <<EOF > $script_dir/config-driver
#!/bin/bash
CC=f1x-cc CXX=f1x-cxx $script_dir/../build.sh $1
EOF

cat <<EOF > $script_dir/build-driver
#!/bin/bash
CC=f1x-cc CXX=f1x-cxx $script_dir/../build.sh $1
EOF

cat <<EOF > $script_dir/test-driver
#!/bin/bash
$script_dir/../test.sh $1 \$@
EOF

chmod +x $script_dir/config-driver
chmod +x $script_dir/build-driver
chmod +x $script_dir/test-driver

cd $src_dir_name
find . -name "*.cache" | xargs rm -rf
