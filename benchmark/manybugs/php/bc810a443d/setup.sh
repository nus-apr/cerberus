script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id
scenario_id=php-bug-2011-11-19-51a4ae6576-bc810a443d
diff_file=Zend/zend_compile.c-51a4ae6576
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

mv $project_name src
cp $dir_name/diffs/${diff_file} $dir_name/src/$(echo $diff_file| cut -d'-' -f 1)
cd $dir_name/src
make distclean &> /dev/null
cp /experiments/benchmark/$benchmark_name/$project_name/base/* $dir_name
# apply libxml fix
cp $dir_name/src $dir_name/src-bk
git reset --hard && git clean -fd
cat ../libxml.patch | patch -p0
./buildconf
PATH_ORIG=$PATH
export PATH=/deps/php/bison-2.2-build/bin:$PATH_ORIG
./configure CFLAGS="-save-temps=obj"
make -j`nproc`
cp $dir_name/src/$(echo $diff_file| cut -d'.' -f 1).i  $dir_name/preprocessed/$(echo $diff_file| cut -d'.' -f 1).c

#./configure CFLAGS="-save-temps=obj"
#make -j`nproc`
cp $dir_name/src/$(echo $diff_file| cut -d'-' -f 1) $dir_name/preprocessed/$(echo $diff_file| cut -d'-' -f 1)
make distclean
./configure && make -j`nproc`


cd $dir_name
chmod +x tester.py test.sh

./tester.py build

cd $dir_name/src-bk
find . -name tests.tar.gz -delete && find . -name tests -type d | tar -czf all-tests.tar.gz --files-from -
mv $dir_name/src-bk/all-tests.tar.gz $dir_name/src/all-tests.tar.gz && rm -rf $dir_name/src-bk
cd $dir_name/src
find . -name tests -type d | rm -rf - && \
    tar -xf all-tests.tar.gz && \
    rm -f all-tests.tar.gz



export PATH=$PATH_ORIG
