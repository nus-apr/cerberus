import multiprocessing as mp
from multiprocessing import TimeoutError
from functools import partial
from app import definitions, values, emitter, utilities
from multiprocessing.dummy import Pool as ThreadPool
import threading
import time
import os
import sys
import re

processed_count = 0


def validate_patch(binary_path, oracle_path, test_id_list, source_file, dir_patch, dir_process, patch_file):
    global processed_count, exit_consume
    test_id_str = ",".join(test_id_list)
    validate_command = "cp {} {};".format(dir_patch + "/" + patch_file, dir_process)
    patch_file = dir_process + "/" + patch_file
    validate_command += "valkyrie --binary={} --test-oracle={} --test-id-list={} " \
                       "--patch-file={} --source={} --test-timeout={} ".format(binary_path,
                                                                               oracle_path,
                                                                               test_id_str,
                                                                               patch_file,
                                                                               source_file,
                                                                               values.DEFAULT_TEST_TIMEOUT)
    validate_command += "--patch-mode=gdb --trace-mode=1 --exec=0 --only-validate > /dev/null 2>&1"
    os.system(validate_command)
    remove_command = "rm -rf {}".format(patch_file)
    os.system(remove_command)
    processed_count += 1


def analyse_output(patch_dir):
    global processed_count
    emitter.normal("\t\t\t analysing output of Valkyrie")
    consumed_count = len(values.LIST_CONSUMED)
    parent_dir = os.path.dirname(patch_dir)
    dir_valid = parent_dir + "/patch-valid"
    dir_invalid = parent_dir + "/patch-invalid"
    dir_error = parent_dir + "/patch-error"
    len_dir_valid = len(os.listdir(dir_valid))
    len_dir_invalid = len(os.listdir(dir_invalid))
    len_dir_error = len(os.listdir(dir_error))
    emitter.highlight("\t\t\t count consumed: {0}".format(consumed_count))
    emitter.highlight("\t\t\t count processed: {0}".format(processed_count))
    emitter.highlight("\t\t\t count valid patches: {0}".format(len_dir_valid))
    emitter.highlight("\t\t\t count invalid patches: {0}".format(len_dir_invalid))
    emitter.highlight("\t\t\t count unsupported patches: {0}".format(len_dir_error))

