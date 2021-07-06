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

    local src1="$directory/src/main/main.c"
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

    local src2="$directory/src/sapi/cli/php_cli.c"
    restore_original $src2
    add-header $src2

    sed -i 's/exit(exit_status);/exit(ANGELIX_OUTPUT(int, exit_status, "exit_status"));/' $src2

#### zend.c ###################################################################

    local src3="$directory/src/Zend/zend.c"
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

    local src4="$directory/src/main/output.c"
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
            local src1="$directory/src/main/output.c"
            restore_original $src1
            ;;
        309579-309580 )
            local src="$directory/src/ext/date/php_date.c"
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
            local src1="$directory/src/ext/standard/url.c"
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
            local src1="$directory/src/ext/standard/string.c"
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
            local src1="$directory/src/Zend/zend_execute.c"
            restore_original $src1
            add-header $src1

            replace-all-in-range "$src1" \
                '^static void zend_fetch_dimension_address_read' \
                95 \
                'return;' \
                'ANGELIX_REACHABLE("return"); return;'

            local src2="$directory/src/main/output.c"
            restore_original $src2
            ;;
        308734-308761 )
            local src1="$directory/src/ext/tokenizer/tokenizer.c"
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

            local src2=".aux/src/php-run-tests.c"
            restore_original $src2

            replace-in-range "$src2" \
                '^int main(int argc, char\*\* argv)' \
                30 \
                'if (num < 0 || num >= length)' \
                'if (num < 0 || num >= length || num == 8208)'
            ;;
        309688-309716 )
            local src1="$directory/src/ext/phar/phar_object.c"
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
            local src1="$directory/src/Zend/zend_closures.c"
            restore_original $src1

            replace-in-range "$src1" \
                '^static void zend_closure_free_storage' \
                10 \
                'zend_closure \*closure = (zend_closure \*)object;' \
                'zend_closure \*closure = (zend_closure \*)object;\
\tzval *c_ptr = closure->this_ptr;'

            local src2=".aux/src/php-run-tests.c"
            restore_original $src2

            replace-in-range "$src2" \
                '^int main(int argc, char\*\* argv)' \
                30 \
                'if (num < 0 || num >= length)' \
                'if (num < 0 || num >= length || num == 1259-1)'
            ;;
        311346-311348 )
            cp $directory/src/Zend/zend_multiply.h $directory/src/Zend/zend_multiply.h.bak
            cp .aux/src/Zend/zend_multiply.h $directory/src/Zend/zend_multiply.h

            cp $directory/src/Zend/zend_vm_execute.h $directory/src/Zend/zend_vm_execute.h.bak
            cp .aux/src/Zend/zend_vm_execute.h $directory/src/Zend/zend_vm_execute.h

            local src1="$directory/src/main/output.c"
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
            local src1="$directory/src/Zend/zend_closures.c"
            restore_original $src1

            replace-in-range "$src1" \
                '^static void zend_closure_free_storage' \
                10 \
                'if (closure->func.type == ZEND_USER_FUNCTION) {' \
                'if (closure->func.type == ZEND_USER_FUNCTION \&\& !closure->this_ptr) {'
            ;;
    esac
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
if [ ! -f "$buggy_directory/INSTRUMENTED_ANGELIX" ]; then
    instrument_test_script $buggy_directory
    touch "$buggy_directory/INSTRUMENTED_ANGELIX"
fi

if [ ! -f "$golden_directory/INSTRUMENTED_ANGELIX" ]; then
    instrument_test_script $golden_directory
    touch "$golden_directory/INSTRUMENTED_ANGELIX"
fi

instrument $buggy_directory
instrument $golden_directory

run_tests_script=$(readlink -f "$root_directory/gmp-run-tests.pl")

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
