script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
scenario_id=gmp-bug-14166-14167
diff_file=mpz/gcdext.c-14166
bug_id=$(echo $scenario_id | rev | cut -d "-" -f 2 | rev)
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/${scenario_id}.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xf ${scenario_id}.tar.gz
mv ${scenario_id} src
rm ${scenario_id}.tar.gz
mv src/* .
rm -rf src
rm -rf  coverage* \
        configuration-oracle \
        local-root \
        limit* \
        *.cache \
        *.debug.* \
        sanity \
        *~ \
        reconfigure \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv $project_name src
cd $dir_name/src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
sed -i "s#_GL_WARN_ON_USE (gets,#//#g" lib/stdio.in.h
sed -i "s#root/mountpoint-genprog/genprog-many-bugs/${scenario_id}/gzip#/data/manybugs/${project_name}/${fix_id}/src#g" tests/Makefile
sed -i "s#\$abs_srcdir#/data/manybugs/${project_name}/${fix_id}/src/tests#g" tests/hufts
chown -R root $dir_name

cd $dir_name/src

mkdir tests/mpbsd/
touch tests/mpbsd/Makefile.in
cp $current_dir/ltmain.sh ltmain.sh
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' configure.in
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile.am

cd $dir_name
## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/${scenario_id}#/data/manybugs/${project_name}/${fix_id}#g" test.sh
sed -i "s#/data/manybugs/${project_name}/${fix_id}/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd ${project_name}#cd src#g" test.sh
sed -i 's#lt-\.\*#lt-\.\* \&\> /dev/null#g' test.sh
sed -i '190d' gmp-run-tests.pl
sed -i '190i my $cmd = sprintf("k=%s && rm -f \\$k && make \\$k && ./\\$k", $name);' gmp-run-tests.pl
chmod +x gmp-run-tests.pl

# fix driver for input generation
sed -i "111d" src/tests/mpz/t-gcd.c
sed -i "111i int reps = atoi(argv[1]); " src/tests/mpz/t-gcd.c
sed -i "111i char* filename = argv[2];" src/tests/mpz/t-gcd.c
sed -i "139i char line1 [1000];\n char line2 [1000];" src/tests/mpz/t-gcd.c
sed -i "141i FILE *file = fopen ( filename, "r" );" src/tests/mpz/t-gcd.c
sed -i "142i if (file != NULL) { fgets(line1,sizeof line1,file);  fgets(line2,sizeof line2,file); fclose(file);  }" src/tests/mpz/t-gcd.c
sed -i "143i else {    perror(filename); }" src/tests/mpz/t-gcd.c
sed -i "145,149d" src/tests/mpz/t-gcd.c
sed -i "145i mpz_set_str (op1, line1, 16);\n mpz_set_str (op2, line2, 16);" src/tests/mpz/t-gcd.c

# Prophet requires/works on source
#hg clone https://gmplib.org/repo/gmp/ src-hg
#cd src-hg; hg update $bug_id
