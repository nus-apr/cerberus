#!/bin/bash
set -euo pipefail
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 4 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
dir_name=/experiment/$benchmark_name/$project_name/$bug_id

version=14166-14167 #this is the angelix version
gold_file=mpz/gcdext.c-$fix_id
diff_file=mpz/gcdext.c-14166

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


instrument () {

}


root_directory=$1
buggy_directory="$root_directory/src"
golden_directory="$root_directory/src-gold"


clean-source $buggy_directory
clean-source $golden_directory


instrument $buggy_directory
instrument $golden_directory


cat <<EOF > $root_directory/angelix/oracle
#!/bin/bash
assert-equal () {
    diff -q <(\$ANGELIX_RUN \$1) <(echo -ne "\$2") > /dev/null
}

case "\$1" in
    1)
        assert-equal "./src/test 1" '0\n'
        ;;
esac
EOF
chmod u+x $root_directory/angelix/oracle


cat <<EOF > $root_directory/angelix/config
#!/bin/bash
date
EOF
chmod +x $root_directory/angelix/config

cat <<EOF > $root_directory/angelix/build
#!/bin/bash
curr=\$(pwd)
echo "BUILDINGTEST"
make -e
EOF
chmod u+x $root_directory/angelix/build

currdir=$(pwd)
