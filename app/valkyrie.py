import multiprocessing as mp
from multiprocessing import TimeoutError
from functools import partial
from app import definitions, values, emitter, utilities
from multiprocessing.dummy import Pool as ThreadPool
import threading
import time
import os
from os.path import isfile, join
from os import listdir
from datetime import datetime


processed_count = 0


def validate_patch(binary_path, oracle_path, test_id_list, source_file, dir_patch, dir_process, patch_file, is_rank):
    global processed_count, exit_consume
    test_id_str = ",".join(test_id_list)
    lib_dir_path = definitions.DIR_LIBS
    link_file = dir_process + "/" + patch_file
    patch_file = dir_patch + "/" + patch_file
    validate_command = "ln -sf {} {};".format(patch_file, link_file)
    timeout = len(test_id_list) * 60
    if binary_path:
        validate_command += "LD_LIBRARY_PATH={} timeout -k1m {}s valkyrie --binary={} --test-oracle={} --test-id-list={} " \
                       "--patch-file={} --source={} --test-timeout={} ".format(lib_dir_path, timeout,
                                                                               binary_path,
                                                                               oracle_path,
                                                                               test_id_str,
                                                                               patch_file,
                                                                               source_file,
                                                                               values.DEFAULT_TEST_TIMEOUT)
    else:
        validate_command += "LD_LIBRARY_PATH={} timeout -k1m {}s valkyrie  --test-suite={} --test-id-list={} " \
                        "--patch-file={} --source={} --test-timeout={} ".format(lib_dir_path, timeout,
                                                                                oracle_path,
                                                                                test_id_str,
                                                                                patch_file,
                                                                                source_file,
                                                                                values.DEFAULT_TEST_TIMEOUT)
    validate_command += "--patch-mode=gdb --trace-mode=1 --exec=0"
    if not is_rank:
        validate_command += "  --only-validate "
    validate_command += " > /dev/null 2>&1"
    os.system(validate_command)
    remove_command = "rm -rf {}".format(link_file)
    os.system(remove_command)
    processed_count += 1
    return patch_file


def compute_latency_valkyrie(start_time_str, tend):
        # Fri 08 Oct 2021 04:59:55 PM +08
        fmt_1 = '%a %d %b %Y %H:%M:%S %p'
        start_time_str = start_time_str.split(" +")[0].strip()
        tstart = datetime.strptime(start_time_str, fmt_1).timestamp()
        duration = (tend - tstart)
        return duration


def analyse_output(patch_dir, time_stamp_start):
    global processed_count
    emitter.normal("\t\t\t analysing output of Valkyrie")
    consumed_count = len(values.LIST_CONSUMED)
    parent_dir = os.path.dirname(patch_dir)
    dir_valid = parent_dir + "/patch-valid"
    dir_invalid = parent_dir + "/patch-invalid"
    dir_error = parent_dir + "/patch-error"
    dir_ranked = parent_dir + "/patch-ranked"
    len_dir_valid = 0
    len_dir_invalid = 0
    len_dir_error = 0
    len_dir_ranked = 0
    time_first_patch = datetime.now().timestamp()

    if dir_valid and os.path.isdir(dir_valid):
        len_dir_valid = len(os.listdir(dir_valid))
    if dir_error and os.path.isdir(dir_error):
        len_dir_error = len(os.listdir(dir_error))
    if dir_invalid and os.path.isdir(dir_invalid):
        len_dir_invalid = len(os.listdir(dir_invalid))
    if dir_ranked and os.path.isdir(dir_ranked):
        len_dir_ranked = len(os.listdir(dir_ranked))

    if dir_valid and os.path.isdir(dir_valid):
        output_patch_list = [join(dir_valid, f) for f in listdir(dir_valid) if isfile(join(dir_valid, f))]
        for output_patch in output_patch_list:
            modified_time = os.lstat(output_patch).st_mtime
            if modified_time < time_first_patch:
                time_first_patch = modified_time
    time_latency = compute_latency_valkyrie(time_stamp_start, time_first_patch)
    emitter.highlight("\t\t\t time latency: {0} seconds".format(time_latency))
    emitter.highlight("\t\t\t count consumed: {0}".format(consumed_count))
    emitter.highlight("\t\t\t count processed: {0}".format(processed_count))
    emitter.highlight("\t\t\t count valid patches: {0}".format(len_dir_valid))
    emitter.highlight("\t\t\t count invalid patches: {0}".format(len_dir_invalid))
    emitter.highlight("\t\t\t count unsupported patches: {0}".format(len_dir_error))
    emitter.highlight("\t\t\t count ranked: {0}".format(len_dir_ranked))

