#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$bug_id
exp_dir_path=/experiment/$benchmark_name/$project_name/$bug_id
setup_dir_path=/setup/$benchmark_name/$project_name/$bug_id
fix_file=$2

cat <<EOF > darjeeling-driver
#!/bin/bash
$setup_dir_path/test.sh /experiment 1 \${1:-}
EOF
chmod +x darjeeling-driver

cat <<EOF > Dockerfile
FROM rshariffdeen/cerberus:darjeeling
USER root
USER root
RUN mkdir -p /setup/$benchmark_name/$project_name/$bug_id
COPY . $setup_dir_path
COPY darjeeling/darjeeling-driver $setup_dir_path
RUN /setup/$benchmark_name/$project_name/$bug_id/setup.sh /experiment
WORKDIR /experiment
EOF

cd $script_dir/..
tag_id=$(echo "$bug_id" | awk '{print tolower($0)}')
docker build -t $tag_id -f darjeeling/Dockerfile .

cat <<EOF > $dir_name/src/repair.yml
version: '1.0'

program:
  image: darjeeling/example:gcd
  language: c
  source-directory: /experiment/source
  build-instructions:
    time-limit: 10
    steps:
      - gcc gcd.c -o gcd
    steps-for-coverage:
      - gcc gcd.c -o gcd --coverage
  tests:
    type: genprog
    workdir: /experiment
    number-of-failing-tests: 1
    number-of-passing-tests: 10
    time-limit: 5

seed: 0
threads: 16
localization:
  type: spectrum
  metric: tarantula
algorithm:
  type: exhaustive
coverage:
  method:
    type: gcov
    files-to-instrument:
      - gcd.c
transformations:
  schemas:
    - type: delete-statement
    - type: replace-statement
    - type: append-statement
resource-limits:
  candidates: 1000
EOF


