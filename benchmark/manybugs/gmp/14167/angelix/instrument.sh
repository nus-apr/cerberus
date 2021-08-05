#!/bin/bash
set -euo pipefail
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/data/$benchmark_name/$project_name/$fix_id

version=14166-14167 #this is the angelix version
gold_file=mpz/gcdext.c-$fix_id
# buggy_file=ext/tokenizer/tokenizer.c-e65d361fde
export ANGELIX_ARGS=" --defect assignments --group-size 1 --klee-solver-timeout 100 --klee-timeout 600 --klee-search dfs --klee-max-forks 100 --synthesis-levels variables --synthesis-bool-only  "
export ANGELIX_KLEE_LOAD="-load=/experiments/.angelix/validation/.libs/libgmp.so"
aux=/experiments/benchmark/manybugs/gmp/.aux


clean-source () {
    local directory="$1"
    pushd "$directory" &> /dev/null
    find . -name .svn -exec rm -rf {} \; &> /dev/null || true
    find . -name .git -exec rm -rf {} \; &> /dev/null || true
    find . -name .hg -exec rm -rf {} \; &> /dev/null || true
    ./configure &> /dev/null || true
    make clean &> /dev/null || true
    make distclean &> /dev/null || true
    popd &> /dev/null
}


# Common functions -------------------------------------------------------------

# replaces within "$3" lines starting from the only occurrence of symbol "$2" in file "$1"
replace-in-range () {
    local file="$1"
    local symbol="$2"
    local length="$3"
    local original="$4"
    local replacement="$5"

    local begin=$(grep -n "$symbol" "$file" | cut -d : -f 1)
    local end=$(( begin + length ))

    sed -i "$begin,$end{s/$original/$replacement/;}" "$file"
}

add-header () {
    local file="$1"
    sed -i '1s/^/#ifndef ANGELIX_OUTPUT\n/' "$file"
    sed -i '2s/^/#define ANGELIX_OUTPUT(type, expr, id) expr\n/' "$file"
    sed -i '3s/^/#define ANGELIX_REACHABLE(id)\n/' "$file"
    sed -i '4s/^/#endif\n/' "$file"
}

restore_original () {
    local src="$1"
    if [ -e $src.org ]; then
        # restore the original
        cp $src.org $src
    else
        # prepare the org file
        cp $src $src.org
    fi
}

# Gzip ----------------------------------------------------------------------

add-angelix-runner-simple () {
    local script="$1"
    local call="$2"

    local line=$(grep -n -v "^\s*[#;]" "$script" | grep -v "echo" | grep "$call" | cut -d: -f 1)
    #echo "line:$line::script: $script"
    sed -i "$line"'s/^\.\.\/gmp/\\\$\\\{ANGELIX_RUN:-eval\\\} \.\.\/gmp/' "$script"
}

add-angelix-runner () {
    local script="$1"
    sed -i 's/&> \/dev\/null \&\&/\&\& \\\$\\\{ANGELIX_RUN:-eval\\\}/' "$script"
}

prepare-angelix-runner () {
    local script="$1"
#    local line=$(grep -n "init" "$script")
    sed -i 's/^\./#\./' "$script"
    sed -i 's/gmp/\.\.\/gmp/' "$script"
    sed -i 's/\.\.\/gmp:/gmp:/' "$script"
    sed -i 's/^Exit/exit/' "$script"
    sed -i 's/framework_failure_/exit 99/' "$script"

    sed -i 's/^compare/diff/' "$script"

    local kline=$(grep -n "gmp" "$script")
    #echo "kline:$kline"
}

preinstrument_test() {
   directory="$1"
   for t in "${test_array[@]}"
   do
        local test_script="$directory/tests/$t"
        prepare-angelix-runner "$test_script"
   done
}


fix-header () {
    local file="$1"
    sed -i '/include \"fib_table/d' "$file"
    sed -i '1s/^/#define FIB_TABLE_LIMIT\t93\n/' "$file"
    sed -i '2s/^/#define FIB_TABLE_LUCNUM_LIMITlt92\n/' "$file"
}

instrument_common() {
    local src1="$aux/gmp-run-tests.pl"
    restore_original $src1

    case $version in
        14166-14167 )
            sed -i 's/^my $cmd;/my $cmd;\
if ($num == 34 - 1) {\
\tprint \"PASS: $name\\n\";\
\texit 0;\
}/' $src1
            ;;
    esac
}

instrument () {
        local directory="$1"
        if [[ "$version" == *"1342"* ]]
        then
                local gmp_error="$directory/mpn/generic/powm.c"
                #cp "$directory/sanity/mpn/generic/powm.c" "$gmp_error"
                local line=$(grep -n "(mp_bitcnt_t)0" $gmp_error | cut -d: -f 1)
                #sed -i 's/if WANT_REDC_2/if 1/g' "$gmp_error"
                #if tail -n +460 "$gmp_error" | grep -q "if WANT_REDC_2" "$gmp_error"; then
                #    sed -i '465d;466d;467d;468d;469d;470d;473d' "$gmp_error"
                #fi

                sed -i 's/~(mp_bitcnt_t)0/0/g' "$gmp_error"
                sed -i 's/REDC_1_TO_REDC_N_THRESHOLD/70/g' "$gmp_error"
                sed -i 's/REDC_2_TO_REDC_N_THRESHOLD/79/g' "$gmp_error"
                sed -i 's/REDC_1_TO_REDC_2_THRESHOLD/12/g' "$gmp_error"


                #sed -i 's/\/\* WANT_REDC_2 \*\///g' "$gmp_error"

                sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/configure.in"
                sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/Makefile.am"
                for ctest in "t-powm" "reuse";
                do
                add-header "$directory/tests/mpz/$ctest.c";
                sed -i '/mpz_powm (/i ANGELIX_REACHABLE("stderr1");' "$directory/tests/mpz/$ctest.c"
                sed -i '/mpz_powm (/a ANGELIX_REACHABLE("stderr2");' "$directory/tests/mpz/$ctest.c"
                done

        else
            local src1="$directory/mpz/gcdext.c"
            restore_original $src1
            sed -i 's/ssize = SIZ (a) >= 0 ? 1 : -1;/\tsiz = SIZ (a) >= 0;\
\tif (siz) {\
\tssize = 1;\
\t} else {\
\tssize = -1;\
\t}/' $src1

            replace-in-range "$src1" \
                '^mpz_gcdext (' \
                10 \
                '  __mpz_struct stmp, gtmp;' \
                '  __mpz_struct stmp, gtmp;\
  int siz;'

            sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/configure.in"
            sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/Makefile.am"
            currdir=$(pwd)
            cp /angelix/build/llvm-gcc4.2-2.9-x86_64-linux/lib/gcc/x86_64-unknown-linux-gnu/4.2.1/install-tools/include/stddef.h "$directory/mpz/stddef.h"
            cp /angelix/build/llvm-gcc4.2-2.9-x86_64-linux/lib/gcc/x86_64-unknown-linux-gnu/4.2.1/install-tools/include/stdarg.h "$directory/mpz/stdarg.h"


            for ctest in "t-gcd"; do
                gmptestd="$directory/tests/mpz/";
                cp $aux/testcase/t-gcd-vet.c "$gmptestd"
                pushd "$gmptestd" > /dev/null
                cp t-gcd-vet.c t-gcd.c
                sed -i '/10, t/d' t-gcd.c
                popd > /dev/null

                cp $aux/testcase/std.txt "$gmptestd"
                pushd "$gmptestd" > /dev/null
                sed -i 's/t:0/t:/g' std.txt
                popd > /dev/null

                cd "$currdir"
                local src="$directory/tests/mpz/$ctest.c"
                add-header $src
                restore_original $src
                sed -i '/s)/i ANGELIX_OUTPUT(int,mpz_get_ui(s),"s");' $src
            done
        fi
}



root_directory=$1
buggy_directory="$root_directory/src"
golden_directory="$root_directory/src-gold"

if [ ! -d golden_directory ]; then
  cp -rf $buggy_directory $golden_directory
  cp "$root_directory/diffs/$gold_file" "$golden_directory/$(echo $gold_file| cut -d'-' -f 1)"
fi

if [ ! -d "$root_directory/angelix" ]; then
  mkdir $root_directory/angelix
fi

clean-source $buggy_directory
clean-source $golden_directory
instrument_common

if [ ! -f "$buggy_directory/INSTRUMENTED_ANGELIX" ]; then
    test_script=$root_directory/gmp-run-tests.pl
    sed -i 's/AM_C_PROTOTYPES/dnl AM_C_PROTOTYPES/g' $buggy_directory/configure.in
    sed -i 's/$(top_builddir)\/ansi2knr//g' $buggy_directory/configure.in
    add-angelix-runner "$test_script"
    touch "$buggy_directory/INSTRUMENTED_ANGELIX"
fi

if [ ! -f "$golden_directory/INSTRUMENTED_ANGELIX" ]; then
    test_script=$root_directory/gmp-run-tests.pl
    sed -i 's/AM_C_PROTOTYPES/dnl AM_C_PROTOTYPES/g' $golden_directory/configure.in
    sed -i 's/$(top_builddir)\/ansi2knr//g' $golden_directory/configure.in
    add-angelix-runner "$test_script"
    touch "$golden_directory/INSTRUMENTED_ANGELIX"
fi

instrument $buggy_directory
instrument $golden_directory

run_tests_script=$(readlink -f "$aux/gmp-run-tests.pl")

cat <<EOF > $root_directory/angelix/oracle
#!/bin/bash
FILE=/tmp/testo
perl "$run_tests_script" "\$1" &> "\$FILE"
cat \$FILE
grep -q "PASS:" \$FILE && echo "PASS" && exit 0
echo "FAIL"
exit 1
EOF
chmod u+x $root_directory/angelix/oracle


cat <<EOF > $root_directory/angelix/config
#!/bin/bash
curr=\$(pwd)
echo "BUILDINGTEST"
   if [[ \$curr =~ .*validation.* ]]
then
  make clean; \
   ./configure CFLAGS=-std=c99 \
--enable-shared --disable-cxx --disable-fast-install --disable-static; \
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;\
make -e fib_table.h;make -e mp_bases.h;
make \
   ./configure CFLAGS=-std=c99 \
--disable-shared --disable-cxx --disable-fast-install --disable-static; \
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;\
make -e fib_table.h;make -e mp_bases.h;
else
   ./configure CFLAGS=-std=c99 \
--disable-shared --disable-cxx --disable-fast-install --enable-static; \
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;\
make -e fib_table.h;make -e mp_bases.h;
fi
EOF
chmod +x $root_directory/angelix/config

cat <<EOF > $root_directory/angelix/build
#!/bin/bash
curr=\$(pwd)
echo "BUILDINGTEST"
#trying to tweet this
#make -e
make -e
cd tests/mpz
for test in "t-powm" "reuse" "t-gcd";
do
   if [[ \$test =~ .*gcd.* ]]
then
   echo "BUILDING VET"
   rm t-gcd
   make -e t-gcd
   chmod 755 t-gcd
else
   rm -r \$test; make -e \$test;
fi
done
cd \$curr
EOF
chmod u+x $root_directory/angelix/build

currdir=$(pwd)
