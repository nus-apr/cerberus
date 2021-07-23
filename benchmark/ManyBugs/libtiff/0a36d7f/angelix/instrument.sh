#!/bin/bash
set -euo pipefail
version=3af26048-72391804 #this is the angelix version
gold_file=libtiff/tif_dirread.c-0a36d7f
aux_dir=/experiments/benchmark/manybugs/libtiff/.aux
export ANGELIX_ARGS="--assert $aux_dir/assert.json"

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

# Libtiff ----------------------------------------------------------------------

add-angelix-runner () {

    local script="$1"
    local call="$2"
    local occurrence="$3"
    local lines=$(grep -n "$call" "$script" | cut -d : -f 1)
    read -a arr <<<$lines #convert list into array
    local line=${arr[$occurrence]}
    sed -i "$line"'s/^/export MEMCHECK=${ANGELIX_RUN:-eval}; /' "$script"
    sed -i "$line"'s/$/&; unset MEMCHECK/' "$script"
}

instrument_test_script () {
    local directory="$1"

    local test22_script="$directory/test/tiffcp-split.sh"
    add-angelix-runner "$test22_script" TIFFCP 0

    local test23_script="$directory/test/tiffcp-split-join.sh"
    add-angelix-runner "$test23_script" TIFFCP 0

    local test28_script="$directory/test/tiff2pdf.sh"
    add-angelix-runner "$test28_script" TIFF2PDF 0

    local test39_script="$directory/test/tiffcrop-extract-logluv-3c-16b.sh"
    add-angelix-runner "$test39_script" TIFFCROP 0

    local test40_script="$directory/test/tiffcrop-extract-minisblack-1c-16b.sh"
    add-angelix-runner "$test40_script" TIFFCROP 0

    local test41_script="$directory/test/tiffcrop-extract-minisblack-1c-8b.sh"
    add-angelix-runner "$test41_script" TIFFCROP 0

    local test43_script="$directory/test/tiffcrop-extract-miniswhite-1c-1b.sh"
    add-angelix-runner "$test43_script" TIFFCROP 0

    local test44_script="$directory/test/tiffcrop-extract-palette-1c-1b.sh"
    add-angelix-runner "$test44_script" TIFFCROP 0

    local test45_script="$directory/test/tiffcrop-extract-palette-1c-4b.sh"
    add-angelix-runner "$test45_script" TIFFCROP 0

    local test46_script="$directory/test/tiffcrop-extract-palette-1c-8b.sh"
    add-angelix-runner "$test46_script" TIFFCROP 0

    local test47_script="$directory/test/tiffcrop-extract-rgb-3c-16b.sh"
    add-angelix-runner "$test47_script" TIFFCROP 0

    local test48_script="$directory/test/tiffcrop-extract-rgb-3c-8b.sh"
    add-angelix-runner "$test48_script" TIFFCROP 0

    local test49_script="$directory/test/tiffcrop-extractz14-logluv-3c-16b.sh"
    add-angelix-runner "$test49_script" TIFFCROP 0

}

instrument () {
    local directory="$1"

    # transformation due to unsupported constructs:
    local dirread_source="$directory/libtiff/tif_dirread.c"
    restore_original $dirread_source
    sed -i 976's/(tsize_t)//' "$dirread_source"
    sed -i 976's/!dir->tdir_count/(dir->tdir_count == 0)/' "$dirread_source"
    sed -i 976's/!w/(w == 0)/' "$dirread_source"

    local test2_source="$directory/test/long_tag.c"
    restore_original $test2_source
    add-header "$test2_source"
    sed -i 's/return 1/return ANGELIX_OUTPUT(int, 1, "longtagreturn")/g' "$test2_source"
    sed -i 's/return 0/return ANGELIX_OUTPUT(int, 0, "longtagreturn")/g' "$test2_source"

    local test3_source="$directory/test/short_tag.c"
    restore_original $test3_source
    add-header "$test3_source"
    sed -i 's/return 1/return ANGELIX_OUTPUT(int, 1, "shorttagreturn")/g' "$test3_source"
    sed -i 's/return 0/return ANGELIX_OUTPUT(int, 0, "shorttagreturn")/g' "$test3_source"

    local test4_source="$directory/test/strip_rw.c"
    restore_original $test4_source
    add-header "$test4_source"
    sed -i 's/return 1/return ANGELIX_OUTPUT(int, 1, "striprwreturn")/g' "$test4_source"
    sed -i 's/return 0/return ANGELIX_OUTPUT(int, 0, "striprwreturn")/g' "$test4_source"

    if [ "$version" != "ee2ce5b7-b5691a5a" ] && [ "$version" != "d13be72c-ccadf48a" ]; then
        local tif_error="$directory/libtiff/tif_error.c"
        restore_original $tif_error
        add-header "$tif_error"
        replace-in-range "$tif_error" 'TIFFError('    5 '{' '{ANGELIX_REACHABLE("TIFFError");'
        replace-in-range "$tif_error" 'TIFFErrorExt(' 5 '{' '{ANGELIX_REACHABLE("TIFFErrorExt");'
    fi

    if [ "$version" == "ee2ce5b7-b5691a5a" ]; then
        local tiff2pdf="$directory/tools/tiff2pdf.c"
        restore_original $tiff2pdf
        add-header "$tiff2pdf"
        sed -i 's/return ret/return ANGELIX_OUTPUT(int, ret, "ret")/' "$tiff2pdf"
    fi


    if [ "$version" == "0661f81-ac6a583" ]; then
        local tif_write="$directory/libtiff/tif_write.c"
        restore_original $tif_write
        add-header "$tif_write"
        replace-in-range "$tif_write" TIFFFlushData1 15 'return (0)' 'return ANGELIX_OUTPUT(int, 0, "flush")'
        replace-in-range "$tif_write" TIFFFlushData1 15 'return (1)' 'return ANGELIX_OUTPUT(int, 1, "flush")'
    fi

    if [ "$version" == "d13be72c-ccadf48a" ]; then
        local src1="$directory/libtiff/tif_warning.c"
        restore_original $src1
        add-header $src1

        replace-in-range "$src1" \
            '^TIFFWarning(' \
            1 \
            '{' \
            '{\
\tANGELIX_OUTPUT(int, strlen(fmt), \"TIFFWarning\");'

        local src2="$directory/tools/tiffcp.c"
        restore_original $src2
        add-header $src2

        replace-in-range "$src2" \
            '^main(' \
            150 \
            'return (-2);' \
            '{ANGELIX_OUTPUT(int, 0, \"TIFFWarning\");\
\t\tANGELIX_OUTPUT(int, -2, \"tiffcp_out\");\
\t\treturn (-2);}'

        replace-in-range "$src2" \
            '^main(' \
            150 \
            'return (-3);' \
            '{ANGELIX_OUTPUT(int, 0, \"TIFFWarning\");\
\t\t\tANGELIX_OUTPUT(int, -3, \"tiffcp_out\");\
\t\t\treturn (-3);}'

        replace-all-in-range "$src2" \
            '^main(' \
            150 \
            'return (1);' \
            'ANGELIX_OUTPUT(int, 0, \"TIFFWarning\");\
\t\t\tANGELIX_OUTPUT(int, 1, \"tiffcp_out\");\
\t\t\treturn (1);'

        replace-in-range "$src2" \
            '^main(' \
            160 \
            'return (0);' \
            'ANGELIX_OUTPUT(int, 0, \"TIFFWarning\");\
\tANGELIX_OUTPUT(int, 0, \"tiffcp_out\");\
\treturn (0);'

        local src3="$directory/libtiff/tif_dirread.c"
        restore_original $src3

        # sed -i "s/} else if (td->td_nstrips > 1/} else if (td->td_stripbytecount[0] != td->td_stripbytecount[1]/" $src3
        # sed -i "s/\&\& td->td_stripbytecount\[0\] \!= td->td_stripbytecount\[1\]/\&\& td->td_nstrips > 1/" $src3
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

run_tests_script=$(readlink -f "$root_directory/libtiff-run-tests.pl")

cat <<EOF > $root_directory/angelix/oracle
#!/bin/bash

if [ "\$1" == "2" ]; then
  cd test
  \$ANGELIX_RUN ./long_tag
elif [ "\$1" == "3" ]; then
  cd test
  \$ANGELIX_RUN ./short_tag
elif [ "\$1" == "4" ]; then
  cd test
  \$ANGELIX_RUN ./strip_rw
else
  perl "$run_tests_script" "\$1" | grep --quiet PASS
fi
EOF
chmod u+x $root_directory/angelix/oracle

cat <<EOF > $root_directory/angelix/config
#!/bin/bash
./configure --disable-nls                                 \
            --disable-shared                              \
            --disable-cxx                                 \
            --disable-jpeg                                \
            --disable-zlib                                \
            --disable-pixarlog                            \
            --disable-jbig;                               \
echo -ne 'all:\nclean:\ndistclean:\n' >> contrib/Makefile
EOF
chmod +x $root_directory/angelix/config

cat <<EOF > $root_directory/angelix/build
#!/bin/bash
make -e
cd test
rm -f long_tag
make -e long_tag
rm -f short_tag
make -e short_tag
rm -f strip_rw
make -e strip_rw
EOF
chmod u+x $root_directory/angelix/build
