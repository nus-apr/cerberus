#!/bin/bash
TEST_ID=$1

cd tests
cp tests/hufts-segv.gz /tmp/

case "$TEST_ID" in
    1) bash helin-segv;;
    2) bash hufts;;
    3) bash memcpy-abuse;;
    4) bash mixed;;
    5) bash null-suffix-clobber;;
    6) bash stdin;;
    7) bash trailing-nul;;
    8) bash zdiff;;
    9) bash zgrep-f;;
    10) bash zgrep-signal;;
    11) bash znew-k;;
esac

ret=$?
exit $ret;

#if [[ ret -eq 1 ]]
#then
#   exit 0;
#else
#
#fi;
