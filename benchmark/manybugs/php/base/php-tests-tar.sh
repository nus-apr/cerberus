#!/bin/bash
TESTREV=$1
#TESTREV=327810
#note: we explicitly exclude ext/posix, because they caused no end of trouble
#IIRC, and is why they're not in the list of directories over which we're
#iterating in the for loop below
SCENARIO=$2
CURREV=$3
for i in `echo "./
Zend/
ext/bcmath/
ext/bz2/
ext/calendar/
ext/com_dotnet/
ext/ctype/
ext/curl/
ext/date/
ext/dba/
ext/dom/
ext/enchant/
ext/ereg/
ext/exif/
ext/fileinfo/
ext/filter/
ext/ftp/
ext/gd/
ext/gettext/
ext/gmp/
ext/hash/
ext/iconv/
ext/imap/
ext/interbase/
ext/intl/
ext/json/
ext/ldap/
ext/libxml/
ext/mbstring/
ext/mcrypt/
ext/mysql/
ext/mysqli/
ext/oci8/
ext/odbc/
ext/openssl/
ext/pcntl/
ext/pcre/
ext/pdo/
ext/pdo_dblib/
ext/pdo_firebird/
ext/pdo_mysql/
ext/pdo_oci/
ext/pdo_odbc/
ext/pdo_pgsql/
ext/pdo_sqlite/
ext/pgsql/
ext/pspell/
ext/phar/
ext/posix/
ext/readline/
ext/reflection/
ext/session/
ext/shmop/
ext/snmp/
ext/soap/
ext/sockets/
ext/simplexml/
ext/skeleton/
ext/spl/examples/
ext/spl/
ext/sqlite3/
ext/standard/
ext/sybase_ct/
ext/sysvmsg/
ext/sysvsem/
ext/sysvshm/
ext/tidy/
ext/tokenizer/
ext/wddx/
ext/xml/
ext/xmlrpc/
ext/xmlreader/
ext/xmlwriter/
ext/xsl/
ext/zip/
ext/zlib/
sapi/
sapi/cgi/
sapi/cli/
"`
do
    pushd $i &> /dev/null && \
    if [[ $? -ne 0 ]]
    then
        echo $i not found
        continue
    fi
    if [[ -d tests/ ]]
    then
	tar cf tests.tar tests
	gzip tests.tar
    fi
    popd &> /dev/null
done