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

max_process_count = mp.cpu_count()
validator_pool = mp.Pool(max_process_count, initializer=mute)
exit_consume = 0
consume_count = 0
result_list = []


def collect_result(result):
    global result_list
    result_list.append(result)


def consume_patches(binary_path, oracle_path, validation_test_list, source_file, dir_patch, dir_process):
    list_dir = os.listdir(dir_patch)
    len_gen = len(list_dir)
    len_consumed = -1
    global exit_consume, consume_count, validator_pool
    dir_base = os.path.dirname(dir_process)
    dir_valid = dir_base + "/patch-valid"
    dir_invalid = dir_base + "/patch-invalid"
    dir_error = dir_base + "/patch-error"
    len_valid = 0
    len_invalid = 0
    len_error = 0
    print(dir_valid, dir_invalid, dir_error)
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
        if len_gen > 0:
            emitter.information("\t\t\t Generated:{} Consumed:{} Processing:{} Valid:{} Invalid:{} Error:{}".format(len_gen,
                                                                                                                    len_consumed,
                                                                                                                    len_processing,
                                                                                                                    len_valid,
                                                                                                                    len_invalid,
                                                                                                                    len_error))
            print(len_gen != len_consumed,values.APR_TOOL_RUNNING,not exit_consume )
        if not values.APR_TOOL_RUNNING:
            len_consumed = len(values.LIST_CONSUMED)
        if not list_dir:
            time.sleep(values.DEFAULT_VALKYRIE_WAIT_TIME)
            continue
        if len_gen == len_consumed:
            time.sleep(1)
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
    global exit_consume, validator_pool
    # Notify threads it's time to exit
    validator_pool.close()
    emitter.normal("\t\t\twaiting for validator completion")
    validator_pool.join()


