#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
TEST_ID=$1
cd $script_dir/tests
cp hufts-segv.gz /tmp/

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

