#!/bin/bash
set -euo pipefail
#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
fix_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=$1/$benchmark_name/$project_name/$fix_id

version=309986-310009 #this is the angelix version
gold_file=Zend/zend_object_handlers.c-$fix_id
# buggy_file=ext/tokenizer/tokenizer.c-e65d361fde
echo "--redundant-test --synthesis-levels extended-logic --synthesis-ptr-vars --klee-max-forks 100 --group-size 1  " > /tmp/ANGELIX_ARGS

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

replace-all-in-range () {
    local file="$1"
    local symbol="$2"
    local length="$3"
    local original="$4"
    local replacement="$5"

    local begin=$(grep -n "$symbol" "$file" | cut -d : -f 1)
    local end=$(( begin + length ))

    sed -i "$begin,$end{s/$original/$replacement/g;}" "$file"
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

add-header () {
    local file="$1"
    sed -i '1s/^/#ifndef ANGELIX_OUTPUT\n/' "$file"
    sed -i '2s/^/#define ANGELIX_OUTPUT(type, expr, id) expr\n/' "$file"
    sed -i '3s/^/#define ANGELIX_REACHABLE(id)\n/' "$file"
    sed -i '4s/^/#endif\n/' "$file"
}

# PHP ----------------------------------------------------------------------

add-angelix-runner () {
    local script="$1"
    local call="$2"
    local line=$(grep -n "$call" "$script" | cut -d : -f 1)
    sed -i "$line"'s/^/(export MEMCHECK=${ANGELIX_RUN:-eval}; /' "$script"
    sed -i "$line"'s/$/)/' "$script"
}

instrument_common () {
    local directory="$1"

####### main.c ################################################################

    local src1="$directory/main/main.c"
    restore_original $src1
    add-header $src1

    sed -i '1s/^/#define NOT_IMPLEMENTED 255\n/' $src1

    sed -i 's/^PHPAPI int (\*php_register_internal_extensions_func)(TSRMLS_D)/\
int _prefix(const char *pre, const char *str)\
{\
\tif (!str || !pre)\
\t\treturn 0;\
\treturn strncmp(pre, str, strlen(pre)) == 0;\
}\
\
PHPAPI int (*php_register_internal_extensions_func)(TSRMLS_D)/g' $src1

    sed -i 's/^PHPAPI int (\*php_register_internal_extensions_func)(TSRMLS_D)/\
int _suffix(const char *suffix, const char *str)\
{\
\tif (!str || !suffix)\
\t\treturn 0;\
\tsize_t lenstr = strlen(str);\
\tsize_t lensuffix = strlen(suffix);\
\tif (lensuffix >  lenstr)\
\t\treturn 0;\
\treturn strncmp(str + lenstr - lensuffix, suffix, lensuffix) == 0;\
}\
\
PHPAPI int (*php_register_internal_extensions_func)(TSRMLS_D)/g' $src1

angelix_output_php_error="va_list args;\n \
\n\
\tif(_prefix(\"is not implemented!\", format)) {\n \
\t\tANGELIX_OUTPUT(int, NOT_IMPLEMENTED, \"php_error\");\n \
\t}"

    replace-in-range "$src1" \
        '^PHPAPI void php_error_docref0' \
        5 \
        'va_list args;' \
        "$angelix_output_php_error"

    replace-in-range "$src1" \
        '^PHPAPI void php_error_docref1' \
        5 \
        'va_list args;' \
        "$angelix_output_php_error"

    replace-in-range "$src1" \
        '^PHPAPI void php_error_docref2' \
        5 \
        'va_list args;' \
        "$angelix_output_php_error"

    replace-in-range "$src1" \
        '^PHPAPI int php_printf' \
        10 \
        'TSRMLS_FETCH();' \
        'TSRMLS_FETCH();\
\tANGELIX_OUTPUT(int, strlen(format), "php_out");'

#### php_cli.c ###################################################################

    local src2="$directory/sapi/cli/php_cli.c"
    restore_original $src2
    add-header $src2

    sed -i 's/exit(exit_status);/exit(ANGELIX_OUTPUT(int, exit_status, "exit_status"));/' $src2

#### zend.c ###################################################################

    local src3="$directory/Zend/zend.c"
    restore_original $src3
    add-header $src3

    sed -i '1s/^/#define ARRAY_TYPE 255\n/' $src3
    sed -i '2s/^/#define OBJECT_TYPE 254\n/' $src3

    sed -i '3s/^/#define OTHER_ZEND_ERROR 255\n/' $src3
    sed -i '4s/^/#define INVALID_ARGUMENT 254\n/' $src3
    sed -i '5s/^/#define UNDEF_PROP 253\n/' $src3
    sed -i '6s/^/#define UNINIT_STR_OFFSET 252\n/' $src3

    sed -i 's/ZEND_PUTS_EX(\"Array\\n\");/ANGELIX_OUTPUT(int, ARRAY_TYPE, \"zend_type\"); ZEND_PUTS_EX(\"Array\\n\");/g' $src3
    sed -i 's/ZEND_PUTS_EX(\" Object\\n\");/ANGELIX_OUTPUT(int, OBJECT_TYPE, \"zend_type\"); ZEND_PUTS_EX(\" Object\\n\");/g' $src3

    replace-in-range "$src3" \
        '^ZEND_API void zend_error' \
        20 \
        'TSRMLS_FETCH();' \
        'TSRMLS_FETCH();\
\tANGELIX_REACHABLE("zend_error");\
\tif(_prefix(\"Invalid argument\", format)) {\
\t\tANGELIX_OUTPUT(int, INVALID_ARGUMENT, \"zend_error\");\
\t}\
\telse if(_prefix(\"Undefined property\", format)) {\
\t\tANGELIX_OUTPUT(int, UNDEF_PROP, \"zend_error\");\
\t}\
\telse if(_prefix(\"Uninitialized string offset\", format)) {\
\t\tANGELIX_OUTPUT(int, UNINIT_STR_OFFSET, \"zend_error\");\
\t}\
\telse {\
\t\tANGELIX_OUTPUT(int, OTHER_ZEND_ERROR, \"zend_error\");\
\t}\
'

#### output.c ###################################################################

    local src4="$directory/main/output.c"
    restore_original $src4
    add-header $src4

    replace-in-range "$src4" \
        '^PHPAPI int php_output_write(const char \*str, size_t len TSRMLS_DC)' \
        10 \
        'return (int) len;' \
        'ANGELIX_OUTPUT(int, (int) len, \"php_output_write\");\
\treturn (int) len;'
}

instrument () {
    local directory="$1"

    case $version in
        307931-307934 )
            local src1="$directory/main/output.c"
            restore_original $src1
            ;;
        309579-309580 )
            local src="$directory/ext/date/php_date.c"
            restore_original $src

            sed -i '1s/^/#define UNKNOWN_OR_BAD_FORMAT 255\n/' $src
            sed -i '2s/^/#define FAILED_TO_PARSE_INTERVAL 254\n/' $src
            sed -i '3s/^/#define DID_NOT_CONTAIN_START_DATE 253\n/' $src
            sed -i '4s/^/#define DID_NOT_CONTAIN_INTERVAL 252\n/' $src
            sed -i '5s/^/#define DID_NOT_CONTAIN_END_DATE 251\n/' $src

            add-header "$src"

            sed -i 's/php_error_docref(NULL TSRMLS_CC, E_WARNING, \"Unknown or bad format (\%s)\", format);/ANGELIX_OUTPUT(int, UNKNOWN_OR_BAD_FORMAT, \"error\"); php_error_docref(NULL TSRMLS_CC, E_WARNING, \"Unknown or bad format (\%s)\", format);/g' $src
            sed -i 's/php_error_docref(NULL TSRMLS_CC, E_WARNING, \"Failed to parse interval (\%s)\", format);/ANGELIX_OUTPUT(int, FAILED_TO_PARSE_INTERVAL, \"error\"); php_error_docref(NULL TSRMLS_CC, E_WARNING, \"Failed to parse interval (\%s)\", format);/g' $src
            sed -i "s/php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain a start date.\", isostr);/ANGELIX_OUTPUT(int, DID_NOT_CONTAIN_START_DATE, \"error\"); php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain a start date.\", isostr);/g" $src
            sed -i "s/php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain an interval.\", isostr);/ANGELIX_OUTPUT(int, DID_NOT_CONTAIN_INTERVAL, \"error\"); php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain an interval.\", isostr);/g" $src
            sed -i "s/php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain an end date or a recurrence count.\", isostr);/ANGELIX_OUTPUT(int, DID_NOT_CONTAIN_END_DATE, \"error\"); php_error_docref(NULL TSRMLS_CC, E_WARNING, \"The ISO interval '%s' did not contain an end date or a recurrence count.\", isostr);/g" $src
            ;;
        309111-309159 )
            local src1="$directory/ext/standard/url.c"
            restore_original $src1
            add-header "$src1"

            sed -i "s/if ((p = memchr(s, '?', (ue - s)))) {/if ((1 != 0) \&\& (p = memchr(s, '?', (ue - s)))) {/g" $src1

            replace-in-range "$src1" \
                '^PHP_FUNCTION(parse_url)' \
                20 \
                'RETURN_FALSE;' \
                'ANGELIX_OUTPUT(int, 0, \"parse_url_out\");\
\t\tRETURN_FALSE;'

            replace-in-range "$src1" \
                '^PHP_FUNCTION(parse_url)' \
                25 \
                'if (key > -1) {' \
                'ANGELIX_OUTPUT(int, strlen(resource->path), \"parse_url_out\");\
\tif (key > -1) {'
            ;;
        309892-309910 )
            local src1="$directory/ext/standard/string.c"
            restore_original $src1
            add-header $src1

            replace-all-in-range "$src1" \
                '^PHP_FUNCTION(substr_compare)' \
               55 \
                'RETURN_FALSE;' \
                'ANGELIX_OUTPUT(int, 0, \"substr_compare_out\");\
\t\tRETURN_FALSE;'

            replace-in-range "$src1" \
                '^PHP_FUNCTION(substr_compare)' \
               80 \
                'zend_binary_strncmp(s1 + offset, (s1_len - offset), s2, s2_len, cmp_len)' \
                'ANGELIX_OUTPUT(int, zend_binary_strncmp(s1 + offset, (s1_len - offset), s2, s2_len, cmp_len), \"substr_compare_out\")'

            replace-in-range "$src1" \
                '^PHP_FUNCTION(substr_compare)' \
               80 \
                'zend_binary_strncasecmp(s1 + offset, (s1_len - offset), s2, s2_len, cmp_len)' \
                'ANGELIX_OUTPUT(int, zend_binary_strncasecmp(s1 + offset, (s1_len - offset), s2, s2_len, cmp_len), \"substr_compare_out\")'
            ;;
        308262-308315 )
            local src1="$directory/Zend/zend_execute.c"
            restore_original $src1
            add-header $src1

            replace-all-in-range "$src1" \
                '^static void zend_fetch_dimension_address_read' \
                95 \
                'return;' \
                'ANGELIX_REACHABLE("return"); return;'

            local src2="$directory/main/output.c"
            restore_original $src2
            ;;
        308734-308761 )
            local src1="$directory/ext/tokenizer/tokenizer.c"
            restore_original $src1

            replace-in-range "$src1" \
                '^static void tokenize' \
                55 \
                'token_line = CG(zend_lineno);' \
                'token_line = CG(zend_lineno);\
\t\tif (0 == 1) break;'

            replace-in-range "$src1" \
                '^static void tokenize' \
                15 \
                'int token_type;' \
                'int token_type = 1;'

            local src2="/experiments/benchmark/manybugs/php/.aux/php-run-tests.c"
            restore_original $src2

            replace-in-range "$src2" \
                '^int main(int argc, char\*\* argv)' \
                30 \
                'if (num < 0 || num >= length)' \
                'if (num < 0 || num >= length || num == 8208)'
            ;;
        309688-309716 )
            local src1="$directory/ext/phar/phar_object.c"
            restore_original $src1

            sed -i 's/if (SUCCESS == zend_hash_find/if (1 \&\& SUCCESS == zend_hash_find/g' $src1
            sed -i 's/if (SUCCESS == phar_split_fname/if (1 \&\& SUCCESS == phar_split_fname/g' $src1

            replace-in-range "$src1" \
                '^PHP_METHOD(Phar, mount)' \
                10 \
                'phar_archive_data \*\*pphar;' \
                'phar_archive_data \*\*pphar;\
\tHashTable *fname_map = \&(PHAR_GLOBALS->phar_fname_map);\
\tulong nNextFreeElement = fname_map->nNextFreeElement;\
\tBucket **arBuckets = fname_map->arBuckets;\
\tzend_bool persistent = fname_map->persistent;\
\tunsigned char nApplyCount = fname_map->nApplyCount;\
\tzend_bool bApplyProtection = fname_map->bApplyProtection;'
            ;;
        310370-310389 )
            local src1="$directory/Zend/zend_closures.c"
            restore_original $src1

            replace-in-range "$src1" \
                '^static void zend_closure_free_storage' \
                10 \
                'zend_closure \*closure = (zend_closure \*)object;' \
                'zend_closure \*closure = (zend_closure \*)object;\
\tzval *c_ptr = closure->this_ptr;'

            local src2="/experiments/benchmark/manybugs/php/.aux/php-run-tests.c"
            restore_original $src2

            replace-in-range "$src2" \
                '^int main(int argc, char\*\* argv)' \
                30 \
                'if (num < 0 || num >= length)' \
                'if (num < 0 || num >= length || num == 1259-1)'
            ;;
        311346-311348 )
            cp $directory/Zend/zend_multiply.h $directory/Zend/zend_multiply.h.bak
            cp /experiments/benchmark/manybugs/php/.aux/Zend/zend_multiply.h $directory/Zend/zend_multiply.h

            cp $directory/Zend/zend_vm_execute.h $directory/Zend/zend_vm_execute.h.bak
            cp /experiments/benchmark/manybugs/php/.aux/Zend/zend_vm_execute.h $directory/Zend/zend_vm_execute.h

            local src1="$directory/main/output.c"
            restore_original $src1
            add-header $src1

            sed -i 's/php_output_write(context.out.data, context.out.used TSRMLS_CC);/ANGELIX_OUTPUT(int, context.out.used, \"php_output\");\n\t\t\tphp_output_write(context.out.data, context.out.used TSRMLS_CC);/g' $src1
            ;;
    esac
}

instrument2 () {
    local directory="$1"

    case $version in
        310370-310389 )
            local src1="$directory/Zend/zend_closures.c"
            restore_original $src1

            replace-in-range "$src1" \
                '^static void zend_closure_free_storage' \
                10 \
                'if (closure->func.type == ZEND_USER_FUNCTION) {' \
                'if (closure->func.type == ZEND_USER_FUNCTION \&\& !closure->this_ptr) {'
            ;;
    esac
}

experiments_dir="$PWD"
test_abbrev="F"
php_oracle_file=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/php-oracle")
php_transform_file=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/php-transform")
test_log_file=php-oracle.log
run_tests_script=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/php-run-tests")
php_helper_script=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/php-helper.php")
aux=$(readlink -f "/experiments/benchmark/manybugs/php/.aux")
main_c_appendix=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/main/main.c.appendix")
php_h_appendix=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/main/php.h.appendix")

root_directory=$1
buggy_directory="$root_directory/src"
golden_directory="$root_directory/src-gold"
restore_original "/experiments/benchmark/manybugs/php/.aux/php-run-tests.c"
# cp "$root_directory/diffs/$buggy_file" "$buggy_directory/$(echo $buggy_file| cut -d'-' -f 1)"
if [ ! -d golden_directory ]; then
  cp -rf $buggy_directory $golden_directory
  cp "$root_directory/diffs/$gold_file"*  "$golden_directory/$(echo $gold_file| cut -d'-' -f 1)"
fi

if [ ! -d "$root_directory/angelix" ]; then
  mkdir $root_directory/angelix
fi

clean-source $buggy_directory
clean-source $golden_directory

if [ ! -f "$buggy_directory/INSTRUMENTED_ANGELIX" ]; then
    instrument_common $buggy_directory
    instrument $buggy_directory
    touch "$buggy_directory/INSTRUMENTED_ANGELIX"
fi

if [ ! -f "$golden_directory/INSTRUMENTED_ANGELIX" ]; then
    instrument_common $golden_directory
    instrument $golden_directory
    instrument2 $golden_directory
    touch "$golden_directory/INSTRUMENTED_ANGELIX"
fi

instrument $buggy_directory
instrument $golden_directory



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
# export AF_SRC_ROOT_DIR=\$(PWD)/php
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


if [[ $test_abbrev == "T" ]]; then
    test_univ=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/TEST_UNIV_ABBREV")
else
    test_univ=$(readlink -f "/experiments/benchmark/manybugs/php/.aux/TEST_UNIV_FULL")
fi

cat <<EOF > $root_directory/angelix/transform
#!/bin/bash
set -uo pipefail

if [ -e configured.mark ]; then
    echo "[php-transform] Already configured"

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
$aux/get_test_script_file.awk $test_univ >> ./main/main.c

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
chmod u+x $root_directory/angelix/transform

cat <<EOF > $root_directory/angelix/config
#!/bin/bash
export PHP_AUTOHEADER=/deps/php/autoconf-2.13-build/bin/autoheader PHP_AUTOCONF=/deps/php/autoconf-2.13-build/bin/autoconf
export PATH=/deps/php/bison-2.2-build/bin:$PATH
# Config libtiff.
make clean
./configure \
  --enable-cli \
  --disable-dom \
  --disable-xmlreader  \
  --disable-xmlwriter  \
  --disable-pear  \
  --disable-pear  \
  --disable-inline-optimization  \
  --without-pcre-dir  \
  --disable-fileinfo \
  --disable-shared
bash $root_directory/angelix/transform
mkdir -p ../state_dump
EOF
chmod +x $root_directory/angelix/config

cat <<EOF > $root_directory/angelix/build
#!/bin/bash
make -e  CFLAGS="-march=x86-64" -j`nproc`
EOF
chmod u+x $root_directory/angelix/build



pushd $aux > /dev/null
sed -i "96,8506d" php-run-tests.c
while IFS= read -r line
do
  sed -i "96i \"$line\"," php-run-tests.c
done < $dir_name/tests.all.txt.rev
gcc -o php-run-tests php-run-tests.c
popd > /dev/null

