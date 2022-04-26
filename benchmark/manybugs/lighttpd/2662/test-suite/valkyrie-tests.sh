#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
TEST_ID=$1
cd $script_dir/tests


case "$TEST_ID" in
    1)  ./core-condition.t ;;
    2)  ./mod-rewrite.t ;;
    3)  ./lowercase.t ;;
    4)  ./mod-redirect.t ;;
    5)  ./mod-secdownload.t ;;
    6)  ./mod-ssi.t ;;
    7)  ./core-var-include.t ;;
    8)  ./core-keepalive.t ;;
    9)  ./mod-cgi.t ;;
    10)  ./core.t ;;
    11)  ./core-request.t ;;
    12)  ./mod-access.t ;;
    13)  ./mod-compress.t ;;
    14)  ./mod-setenv.t ;;
    15)  ./fastcgi.t ;;
    16)  ./cachable.t ;;
    17)  ./mod-userdir.t ;;
    18)  ./core-response.t ;;
    19)  ./request.t ;;
    20)  ./mod-auth.t ;;
    21)  ./symlink.t ;;
esac
ret=$?
exit $ret;

