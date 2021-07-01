script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
scenario_id=php-bug-2011-02-27-e65d361fde-1d984a7ffd
diff_file=ext/tokenizer/tokenizer.c-e65d361fde
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
        php-tests-* \
        *.cache \
        *.debug.* \
        *~ \
        php.tar.gz && \
    mv test.sh test.sh.orig && \
    mv bug-failures bug-info && \
    cp bugged-program.txt manifest.txt && \
    mv *.lines bug-info && \
    mv fix-failures bug-info

chown -R root $dir_name
grep -o -P '(?<=")[^"]+.phpt(?=")' php-run-tests.c > tests.all.txt
grep -o -P '\d+(?= &&)' test.sh.orig > tests.indices.txt
rm -f php-run-tests.c test.sh.orig
mv $project_name src
cd $dir_name/src
make distclean &> /dev/null && \
    rm -rf  configure config.nice autom4te.cache aclocal.m4 php5.spec missing mkinstalldirs
cd $dir_name
cp /experiments/benchmark/$benchmark_name/$project_name/base/* $dir_name
cd src && git reset --hard && git clean -fd && git checkout $bug_id
# apply libxml fix
cat libxml.patch | patch -p0
# build configure script
./buildconf

./configure CFLAGS="-save-temps=obj"
make -j`nproc`
cp $dir_name/src/$(echo $diff_file| cut -d'-' -f 1) $dir_name/preprocessed/$(echo $diff_file| cut -d'-' -f 1)
make distclean


./tester.py build && rm tests.all.txt tests.indices.txt
cd $dir_name/src
find . -name tests.tar.gz -delete && find . -name tests -type d | tar -czf all-tests.tar.gz --files-from -
find . -name tests -type d | rm -rf - && \
    tar -xf all-tests.tar.gz && \
    rm -f all-tests.tar.gz







