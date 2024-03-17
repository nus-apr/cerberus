#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id
exp_dir_path=/experiment/$benchmark_name/$project_name/$bug_id
setup_dir_path=/setup/$benchmark_name/$project_name/$bug_id

# do whatevey you can after this line.
cd /zap
java -jar jenkins.war & 
