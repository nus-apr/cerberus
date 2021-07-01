#!/usr/bin/env python
import os
import shutil
import subprocess
import multiprocessing

NASTY_REVISIONS = [
    "1f49902999",
    "147382033a",
    "e7a1d5004e",
    "0a1cc5f01c",
    "51a4ae6576",
    "eeba0b5681",
    "fefe9fc5c7",
    "0169020e49",
    "eeba0b5681",
    "2568672691",
    "c4eb5f2387",
    "032d140fd6",
    "c1322d2505",
    "f5a9e17f9c",
    "ff63c09e6f"
]

# keep a list of test directories
# find . -name tests -type d -exec git checkout FIX-REVISION {} \;
TEST_DIRS = [
    "Zend/tests",
    "tests",
    "ext/date/tests"
    "ext/dom/tests"
    "ext/libxml/tests",
    "ext/json/tests",
    "ext/phar/tests",
    "ext/reflection/tests",
    "ext/spl/tests",
    "ext/sessions/tests",
    "ext/simplexml/tests",
    "ext/standard/tests",
    "ext/sqlite3/tests"
]


def cmd(cmd):
    subprocess.check_call(cmd, shell=True)


if __name__ == "__main__":
    bug_rev = os.environ.get('BUG_REVISION')

    with open('/experiment/manifest.txt', 'r') as f:
        buggy_files = [l.strip() for l in f]

    # handle nasty scenarios
    if bug_rev in NASTY_REVISIONS:
        cmd('cd /experiment/src && git reset --hard && git clean -fd')
        cmd('cd /experiment/src && git checkout "{}"'.format(bug_rev))

    # apply libxml fix
    cmd('cd /experiment/src && cat ../libxml.patch | patch -p0')

    # build configure script
    cmd('cd /experiment/src && ./buildconf')

    # preprocess
    if bug_rev in NASTY_REVISIONS:
        cmd('cd /experiment/src && ./configure CFLAGS="-save-temps=obj"')
        cmd('cd /experiment/src && make -j{}'.format(multiprocessing.cpu_count()))

        for fn in buggy_files:
            source_fn = fn.replace('.c', '.i').replace('.h', '.i')
            source_fn = os.path.join('/experiment/src', source_fn)
            target_fn = os.path.join('/experiment/preprocessed', fn)
            os.remove(target_fn)
            os.rename(source_fn, target_fn)

        cmd('cd /experiment/src && make distclean')

    # configure and build source code
    cmd('cd /experiment/src && ./configure')
    cmd('cd /experiment/src && make -j{}'.format(multiprocessing.cpu_count()))