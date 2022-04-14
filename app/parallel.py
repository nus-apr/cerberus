import multiprocessing as mp
from multiprocessing import TimeoutError
from functools import partial
from app import definitions, values, emitter, utilities, valkyrie
from multiprocessing.dummy import Pool as ThreadPool
import threading
import time
import os
import sys
import re


def mute():
    sys.stdout = open(os.devnull, 'w')
    sys.stderr = open(os.devnull, 'w')


max_process_count = 200
validator_pool = mp.Pool(max_process_count, initializer=mute)
exit_consume = 0
consume_count = 0
result_list = []
len_gen = 0
len_processed = 0


def collect_result(result):
    global result_list
    result_list.append(result)


def consume_patches(binary_path, oracle_path, validation_test_list, source_file, dir_patch, dir_process):
    global exit_consume, consume_count, validator_pool, len_gen, len_processed
    list_dir = os.listdir(dir_patch)
    len_gen = len(list_dir)
    len_consumed = -1
    dir_base = os.path.dirname(dir_process)
    dir_valid = dir_base + "/patch-valid"
    dir_invalid = dir_base + "/patch-invalid"
    dir_error = dir_base + "/patch-error"
    len_valid = 0
    len_invalid = 0
    len_error = 0
    while len_gen != len_consumed or values.APR_TOOL_RUNNING or not exit_consume:
        list_dir = os.listdir(dir_patch)
        len_gen = len(list_dir)
        if os.path.isdir(dir_valid):
            len_valid = len(os.listdir(dir_valid))
        if os.path.isdir(dir_invalid):
            len_invalid = len(os.listdir(dir_invalid))
        if os.path.isdir(dir_error):
            len_error = len(os.listdir(dir_error))
        len_processing = len(os.listdir(dir_process))
        len_processed = len(result_list)
        if len_gen > 0:
            emitter.information("\t\t\t Generated:{} Consumed:{} Processed: {}"
                                " Processing:{} Valid:{} Invalid:{} Error:{}".format(len_gen,
                                                                                     len_consumed,
                                                                                     len_processed,
                                                                                     len_processing,
                                                                                     len_valid,
                                                                                     len_invalid,
                                                                                     len_error))
        if not values.APR_TOOL_RUNNING:
            len_consumed = len(values.LIST_CONSUMED)
        if not list_dir:
            time.sleep(values.DEFAULT_VALKYRIE_WAIT_TIME)
            continue
        if len_gen == len_consumed:
            time.sleep(3)
            continue
        list_selected = list(set(list_dir) - set(values.LIST_CONSUMED))[:1000]
        for patch_file in list_selected:
            validator_pool.apply_async(valkyrie.validate_patch,
                                       args=(binary_path, oracle_path, validation_test_list, source_file, dir_patch,
                                             dir_process, patch_file),
                                       callback=collect_result)

            consume_count += 1
        values.LIST_CONSUMED = values.LIST_CONSUMED + list_selected
        len_consumed = len(values.LIST_CONSUMED)


def wait_validation():
    global exit_consume, validator_pool, len_gen, consume_count, len_processed
    # Notify threads it's time to exit
    time.sleep(5)
    while len_gen != consume_count:
        pass
    validator_pool.close()
    emitter.normal("\t\t\twaiting for validator completion")
    while len_gen != len_processed:
        pass
    validator_pool.join()
    exit_consume = 1



