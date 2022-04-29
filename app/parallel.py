import multiprocessing as mp
from multiprocessing import TimeoutError
from functools import partial
from app import definitions, values, emitter, utilities, valkyrie
from multiprocessing.dummy import Pool as ThreadPool
import subprocess
import time
import os
import sys
import re


def mute():
    sys.stdout = open(os.devnull, 'w')
    sys.stderr = open(os.devnull, 'w')


max_process_count = 1
validator_pool = None
exit_consume = 0
consume_count = 0
result_list = []
len_gen = 0
len_processed = 0
timeout = 0


def initialize():
    global validator_pool, exit_consume, consume_count, len_gen, len_processed, timeout, result_list
    if values.DEFAULT_USE_VTHREADS:
        validator_pool = mp.Pool(max_process_count, initializer=mute)
    exit_consume = 0
    consume_count = 0
    result_list = []
    len_gen = 0
    len_processed = 0
    timeout = 0
    values.LIST_CONSUMED = []


def collect_result(result):
    global result_list
    result_list.append(result)


def consume_patches(path_info, dir_info, config_info):
    global exit_consume, consume_count, validator_pool, len_gen, len_processed, timeout

    binary_path, oracle_path, source_file = path_info
    dir_patch, dir_process = dir_info
    _, _, total_timeout, _ = config_info

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
    time.sleep(5)
    while len_gen != len_consumed or values.APR_TOOL_RUNNING or not exit_consume:
        list_dir = os.listdir(dir_patch)
        len_gen = len(list_dir)
        if time.time() > total_timeout:
            break
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
        if values.DEFAULT_USE_VTHREADS:
            list_selected = list(set(list_dir) - set(values.LIST_CONSUMED))[:1000]
        else:
            list_selected = list(set(list_dir) - set(values.LIST_CONSUMED))[:100]
        for patch_file in list_selected:
            file_info = (binary_path, oracle_path, source_file, patch_file)
            if values.DEFAULT_USE_VTHREADS:
                validator_pool.apply_async(valkyrie.validate_patch,
                                           args=(dir_info, file_info, config_info),
                                           callback=collect_result)
            else:
                result_list.append(valkyrie.validate_patch(dir_info, file_info, config_info))


            consume_count += 1
        values.LIST_CONSUMED = values.LIST_CONSUMED + list_selected
        len_consumed = len(values.LIST_CONSUMED)


def wait_validation():
    global exit_consume, validator_pool, len_gen, consume_count, len_processed, timeout
    # Notify threads it's time to exit
    time.sleep(5)
    while len_gen != consume_count and time.time() <= timeout:
        pass
    if values.DEFAULT_USE_VTHREADS:
        validator_pool.close()
    emitter.normal("\t\t\twaiting for validator completion")
    while len_gen != len_processed and time.time() <= timeout:
        pass
    emitter.normal("\t\t\tterminating validator")
    if values.DEFAULT_USE_VTHREADS:
        validator_pool.terminate()
        validator_pool.join()
    exit_consume = 1



