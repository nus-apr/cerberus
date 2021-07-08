script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
src_dir_name=/data/$benchmark_name/$project_name/$fix_id/src
test_dir_name=/data/$benchmark_name/$project_name/$fix_id/tests
target_dir=/experiments/benchmark/$benchmark_name/$project_name/$fix_id
cd $test_dir_name

# Create Seed Files
mkdir $target_dir/seed-dir
echo "76429e12e4fdd8929d89c21657097fbac09d1dc08cf7f1323a34e78ca34226e1a7a29b86fee0fa7fe2cc2a183d46d50df1fe7029590974ad7da77605f35f902cb8b9b8d22dd881eaae5919675d49a337145a029c3b33fc2b0" > $target_dir/seed-dir/seed-1.txt;
echo "4da8e405e0d2f70d6d679d3de08a5100a81ec2cff40f97b313ae75e1183f1df2b244e194ebb02a4ece50d943640a301f0f6cc7f539117b783c3f3a3f91649f8a00d2e1444d52722810562bce02fccdbbc8fe3276646e306e723dd3b" >> $target_dir/seed-dir/seed-1.txt;
echo "4da8e405e0d2f70d6d679d3de08a5100a81ec2cff40f97b313ae75e1183f1df2b244e194ebb02a4ece50d943640a301f0f6cc7f539117b783c3f3a3f91649f8a00d2e1444d52722810562bce02fccdbbc8fe3276646e306e723dd3b" > $target_dir/seed-dir/seed-2.txt;
echo "76429e12e4fdd8929d89c21657097fbac09d1dc08cf7f1323a34e78ca34226e1a7a29b86fee0fa7fe2cc2a183d46d50df1fe7029590974ad7da77605f35f902cb8b9b8d22dd881eaae5919675d49a337145a029c3b33fc2b0" >> $target_dir/seed-dir/seed-2.txt;

cd $src_dir_name
make clean

if [ ! -f "$src_dir_name/INSTRUMENTED_FIX2FIT" ]; then
    touch "$src_dir_name/INSTRUMENTED_FIX2FIT"
fi
