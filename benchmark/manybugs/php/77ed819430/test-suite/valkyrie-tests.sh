#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
TEST_ID=$1
./tester.py run $TEST_ID
ret=$?
exit $ret;

