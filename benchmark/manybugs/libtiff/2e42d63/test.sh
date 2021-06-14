script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$bug_id
scenario_id=libtiff-bug-2009-02-05-764dbba-2e42d63
cd $dir_name
TEST_ID=$1
POS_N=64
NEG_N=9

## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#/data/manybugs/libtiff/${bug_id}#g" test.sh
sed -i "s#/data/manybugs/libtiff/${bug_id}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd libtiff#cd src#g" test.sh


if [ -z "$TEST_ID" ]
then
   # Run passing test cases
  for i in `seq -s " " -f "p%g"  1 $POS_N`
  do
  bash test.sh $i /data
  done

  # Run failing test cases
  for i in `seq -s " " -f "n%g"  1 $NEG_N`
  do
  bash test.sh $i /data
  done
else
  cd $dir_name/src
  timeout 5 perl $dir_name/libtiff-run-tests.pl $TEST_ID
fi
