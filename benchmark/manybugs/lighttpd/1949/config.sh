#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
benchmark_name=$(echo $script_dir | rev | cut -d "/" -f 3 | rev)
project_name=$(echo $script_dir | rev | cut -d "/" -f 2 | rev)
bug_id=$(echo $script_dir | rev | cut -d "/" -f 1 | rev)
dir_name=/data/$benchmark_name/$project_name/$bug_id
cd $dir_name/src

# Config lighttpd.
make clean
./configure CFLAGS='-g -O0' --enable-static \
            --with-pcre=yes \
            --with-ldap \
            --with-bzip2 \
            --with-openssl \
            --with-gdbm \
            --with-memcache \
            --with-webdav-props \
            --with-webdav-locks;
