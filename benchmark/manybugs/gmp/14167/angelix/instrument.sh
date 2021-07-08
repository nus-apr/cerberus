#!/bin/bash
set -euo pipefail
version=14166-14167 #this is the angelix version
gold_file=mpz/gcdext.c-14167

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
        local test_script="$directory/src/tests/$t"
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
    local src1=".aux/gmp/gmp-run-tests.pl"
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
                local gmp_error="$directory/src/mpn/generic/powm.c"
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

                sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/src/configure.in"
                sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/src/Makefile.am"
                for ctest in "t-powm" "reuse";
                do
                add-header "$directory/src/tests/mpz/$ctest.c";
                sed -i '/mpz_powm (/i ANGELIX_REACHABLE("stderr1");' "$directory/src/tests/mpz/$ctest.c"
                sed -i '/mpz_powm (/a ANGELIX_REACHABLE("stderr2");' "$directory/src/tests/mpz/$ctest.c"
                done

        else
            local src1="$directory/src/mpz/gcdext.c"
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

            sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/src/configure.in"
            sed -i 's/no-dependencies ansi2knr/no-dependencies/g' "$directory/src/Makefile.am"
            currdir=$(pwd)
            cp /angelix/build/llvm-gcc4.2-2.9-x86_64-linux/lib/gcc/x86_64-unknown-linux-gnu/4.2.1/install-tools/include/stddef.h "$directory/src/mpz/stddef.h"
            cp /angelix/build/llvm-gcc4.2-2.9-x86_64-linux/lib/gcc/x86_64-unknown-linux-gnu/4.2.1/install-tools/include/stdarg.h "$directory/src/mpz/stdarg.h"


            for ctest in "t-gcd"; do
                gmptestd="$directory/src/tests/mpz/";
                cp .aux/gmp/testcase/t-gcd-vet.c "$gmptestd"
                pushd "$gmptestd" > /dev/null
                cp t-gcd-vet.c t-gcd.c
                sed -i '/10, t/d' t-gcd.c
                popd > /dev/null

                cp .aux/gmp/testcase/std.txt "$gmptestd"
                pushd "$gmptestd" > /dev/null
                sed -i 's/t:0/t:/g' std.txt
                popd > /dev/null

                cd "$currdir"
                local src="$directory/src/tests/mpz/$ctest.c"
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
    test_script=$buggy_directory/gmp-run-tests.pl
    sed -i 's/AM_C_PROTOTYPES/dnl AM_C_PROTOTYPES/g' $buggy_directory/src/configure.in
    sed -i 's/$(top_builddir)\/ansi2knr//g' $buggy_directory/src/configure.in
    add-angelix-runner "$test_script"
    touch "$buggy_directory/INSTRUMENTED_ANGELIX"
fi

if [ ! -f "$golden_directory/INSTRUMENTED_ANGELIX" ]; then
    test_script=$golden_directory/gmp-run-tests.pl
    sed -i 's/AM_C_PROTOTYPES/dnl AM_C_PROTOTYPES/g' $golden_directory/src/configure.in
    sed -i 's/$(top_builddir)\/ansi2knr//g' $golden_directory/src/configure.in
    add-angelix-runner "$test_script"
    touch "$golden_directory/INSTRUMENTED_ANGELIX"
fi

instrument $buggy_directory
instrument $golden_directory

run_tests_script=$(readlink -f "$root_directory/gmp-run-tests.pl")

cat <<EOF > $root_directory/angelix/oracle
#!/bin/bash
set -uo pipefail

test_log_file=$test_log_file

if [ "\$#" -ne 1 ]
then
    echo "Usage: \$0 <test-id>" >> \${test_log_file}
    exit 1
fi


#################################################################

CMD=\$(basename \$0 | sed 's/.\///' | sed 's/.sh//')

function abort() {
    local msg=\$1
    abort_msg="[\$CMD] Abort: \$msg"
    echo "\$abort_msg" >> \${test_log_file} 2>& 1
    exit 1
}

#################################################################

test_id="\$1"

run_tests_script="$run_tests_script"
if ! [ -e \$run_tests_script ]; then
    abort "No such file: \$run_tests_script"
fi

# the current dir is {validation, frontend, backend}.
# export AF_WORK_DIR=\$(readlink -f .)
# export AF_SRC_ROOT_DIR=\$(pwd)/php
# export AF_USE_TEST_SCRIPT_ID=""

if ! [ -e ../php-helper.php ]; then
    cp $php_helper_script ..
fi

test_abbrev="$test_abbrev"
if [[ \$test_abbrev == "T" ]]; then
    echo "[oracle] \${run_tests_script} \${test_id} 'T'" >> \${test_log_file} 2>& 1
    \${run_tests_script} \${test_id} 'T'
    result=\$?
else
    echo "[oracle] \${run_tests_script} \${test_id} 'F'" >> \${test_log_file} 2>& 1
    \${run_tests_script} \${test_id} 'F'
    result=\$?
fi

echo "[oracle] test result: \$result" >> \${test_log_file} 2>& 1

if [[ \$result -eq 0 ]]; then
    echo "\${test_id}: P" >> \${test_log_file} 2>& 1
    exit 0
else
    echo "\${test_id}: N" >> \${test_log_file} 2>& 1
    exit 1
fi
EOF
chmod u+x $root_directory/angelix/oracle


cat <<EOF > $root_directory/angelix/transform
#!/bin/bash
set -uo pipefail

if [ -e configured.mark ]; then
    echo "[transform] Already configured"

    # Makefile
    sed -i 's/all_targets = \$(OVERALL_TARGET) \$(PHP_MODULES) \$(PHP_ZEND_EX) \$(PHP_BINARIES) pharcmd/all_targets = \$(OVERALL_TARGET) \$(PHP_MODULES) \$(PHP_ZEND_EX) \$(PHP_BINARIES)/' ./Makefile
    sed -i 's/PHP_BINARIES = cli cgi/PHP_BINARIES = cli/' ./Makefile

    exit 0
fi

# extend main.c
cp $main_c_appendix ./main/
cat ./main/main.c ./main/main.c.appendix > ./main/main.c.merge
cp ./main/main.c ./main/main.c.bak
cp ./main/main.c.merge ./main/main.c
$aux/src/get_test_script_file.awk $test_univ >> ./main/main.c

# extend php.h
cp $php_h_appendix ./main/
cp ./main/php.h ./main/php.h.bak
cat ./main/php.h ./main/php.h.appendix > ./main/php.h.merge
cp ./main/php.h.merge ./main/php.h

files=\$(grep -rl "FD_ZERO(" --include=*.c) || true
for file in \$files; do
    sed -i 's/FD_ZERO(/FD_ZERO_SIMUL(/g' \$file
done

files=\$(grep -rl "(char \*)gnu_get_libc_version()" --include=*.c) || true
for file in \$files; do
    sed -i 's/(char \*)gnu_get_libc_version()/\"2.19\"/g' \$file
done

files=\$(grep -rl "# define XPFPA_HAVE_CW 1" --include=*.h) || true
for file in \$files; do
    sed -i 's/# define XPFPA_HAVE_CW 1//g' \$file
done

files=\$(grep -rl "#define HAVE_MMAP 1" --include=*.h) || true
for file in \$files; do
    sed -i 's/#define HAVE_MMAP 1//g' \$file
done

# php_crypt_r.c
sed -i 's/#elif (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 2))/#elif defined(AF_KEEP_ORG) \&\& (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 2))/g' ./ext/standard/php_crypt_r.c
sed -i 's/#elif (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 1))/#elif defined(AF_KEEP_ORG) \&\& (defined(__GNUC__) \&\& (__GNUC__ >= 4 \&\& __GNUC_MINOR__ >= 1))/g' ./ext/standard/php_crypt_r.c
sed -i 's/#elif defined(HAVE_ATOMIC_H)/#elif defined(AF_KEEP_ORG) \&\& defined(HAVE_ATOMIC_H)/g' ./ext/standard/php_crypt_r.c

# zend_alloc.c
sed -i 's/#if defined(__GNUC__) && defined(i386)/#if defined(AF_KEEP_ORG) \&\& defined(__GNUC__) \&\& defined(i386)/g' ./Zend/zend_alloc.c
sed -i 's/#elif defined(__GNUC__) && defined(__x86_64__)/#elif defined(AF_KEEP_ORG) \&\& defined(__GNUC__) \&\& defined(__x86_64__)/g' ./Zend/zend_alloc.c
sed -i 's/#elif defined(_MSC_VER) && defined(_M_IX86)/#elif defined(AF_KEEP_ORG) \&\& defined(_MSC_VER) \&\& defined(_M_IX86)/g' ./Zend/zend_alloc.c

# zend_language_scanner.c
if [ \$(basename \`pwd\`) == "backend" ]; then
    sed -i 's/SCNG(yy_start) = (unsigned char \*)buf - offset;/load_data\(\&buf, \&offset, \&size, file_handle->filename\); SCNG\(yy_start\) = \(unsigned char \*\)buf-offset;/g' ./Zend/zend_language_scanner.c
else
    sed -i 's/SCNG(yy_start) = (unsigned char \*)buf - offset;/if (getenv("ANGELIX_TRACE")) dump_data\(buf, offset, size, file_handle->filename\); SCNG\(yy_start\) = \(unsigned char \*\)buf-offset;/g' ./Zend/zend_language_scanner.c
fi

# zend.h
sed -i 's/# define EXPECTED(condition)   __builtin_expect(condition, 1)/# define EXPECTED(condition)   (__builtin_expect(condition, 1))/g' ./Zend/zend.h
sed -i 's/# define UNEXPECTED(condition) __builtin_expect(condition, 0)/# define UNEXPECTED(condition) (__builtin_expect(condition, 0))/g' ./Zend/zend.h

# php_cli.c
sed -i 's/script_file=argv\[php_optind\];/script_file = get_script_file\(argv\[php_optind\]\);/g' ./sapi/cli/php_cli.c

# Makefile
sed -i 's/all_targets = \$(OVERALL_TARGET) \$(PHP_MODULES) \$(PHP_ZEND_EX) \$(PHP_BINARIES) pharcmd/all_targets = \$(OVERALL_TARGET) \$(PHP_MODULES) \$(PHP_ZEND_EX) \$(PHP_BINARIES)/' ./Makefile
sed -i 's/PHP_BINARIES = cli cgi/PHP_BINARIES = cli/' ./Makefile

touch configured.mark

exit 0
EOF



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
make -j`nproc`
cd \$curr
EOF
chmod u+x $root_directory/angelix/build

currdir=$(pwd)
