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
import queue

queueLock = threading.Lock()
workQueue = queue.Queue()
threads = []
max_thread_count = mp.cpu_count()
thread_count = 0
exit_flag = 0
consume_count = 0
processed_count = 0


class myThread(threading.Thread):
    global exit_flag
    def __init__(self, threadID, name, queue, binary_path, oracle_path, test_id_str, source_file):
        threading.Thread.__init__(self)
        self.threadID = threadID
        self.name = name
        self.queue = queue
        self.binary_path = binary_path
        self.oracle_path = oracle_path
        self.test_id_str = test_id_str
        self.source_file = source_file

    def run(self):
        validate(self)


def validate(thread):
    global exit_flag, queueLock, workQueue, processed_count
    while not exit_flag:
        queueLock.acquire()
        if not workQueue.empty():
            patch_file = thread.queue.get()
            queueLock.release()
            validate_command = "valkyrie --binary={} --test-oracle={} --test-id-list={} " \
                               "--patch-file={} --source={} --test-timeout={} ".format(thread.binary_path,
                                                                                       thread.oracle_path,
                                                                                       thread.test_id_str,
                                                                                       patch_file,
                                                                                       thread.source_file,
                                                                                       values.DEFAULT_TEST_TIMEOUT)
            validate_command += "--patch-mode=gdb --trace-mode=1 --exec=0"
            utilities.execute_command(validate_command)
            utilities.execute_command("rm -rf {}".format(patch_file))
            processed_count += 1

        else:
            queueLock.release()
            time.sleep(1)


def init_threads(binary_path, oracle_path, validation_test_list, source_file):
    global thread_count, workQueue
    test_id_str = ",".join(validation_test_list)
    for t_id in range(0, max_thread_count):
        t_name = "t_{}".format(t_id)
        thread = myThread(t_id, t_name, workQueue, binary_path, oracle_path, test_id_str, source_file)
        thread.start()
        threads.append(thread)
        thread_count += 1


def consume_patches(patch_dir, process_dir, consume_limit, max_limit):
    list_dir = os.listdir(patch_dir)
    len_gen = len(list_dir)
    len_processed = -1
    global workQueue, queueLock, exit_flag, consume_count
    while len_gen != len_processed or values.APR_TOOL_RUNNING:
        list_dir = os.listdir(patch_dir)
        len_gen = len(list_dir)
        if not values.APR_TOOL_RUNNING:
            len_processed = len(values.LIST_PROCESSED)
        if not list_dir:
            time.sleep(values.DEFAULT_VALKYRIE_WAIT_TIME)
            continue
        list_selected = list(set(list_dir) - set(values.LIST_PROCESSED))
        queueLock.acquire()
        for patch_file in list_selected:
            utilities.execute_command("cp {} {}".format(patch_dir + "/" + patch_file, process_dir))
            workQueue.put(process_dir + "/" + patch_file)
            consume_count += 1
        queueLock.release()
        emitter.information("Generated:{} Consumed:{} Processed:{}".format(len_gen, consume_count, processed_count))
        values.LIST_PROCESSED = values.LIST_PROCESSED + list_selected
        len_processed = len(values.LIST_PROCESSED)

    # Wait for queue to empty
    while not workQueue.empty():
        pass


def wait_validation():
    global exit_flag, threads
    # Notify threads it's time to exit
    exit_flag = 1
    # Wait for all threads to complete
    for t in threads:
        t.join()


def analyse_output(patch_dir):
    global consume_count, processed_count
    parent_dir = os.path.dirname(patch_dir)
    dir_valid = parent_dir + "/patch-valid"
    dir_invalid = parent_dir + "/patch-invalid"
    dir_error = parent_dir + "/patch-error"
    len_dir_valid = len(os.listdir(dir_valid))
    len_dir_invalid = len(os.listdir(dir_invalid))
    len_dir_error = len(os.listdir(dir_error))
    emitter.highlight("\t\t\t count consumed: {0}".format(consume_count))
    emitter.highlight("\t\t\t count processed: {0}".format(processed_count))
    emitter.highlight("\t\t\t count valid patches: {0}".format(len_dir_valid))
    emitter.highlight("\t\t\t count invalid patches: {0}".format(len_dir_invalid))
    emitter.highlight("\t\t\t count unsupported patches: {0}".format(len_dir_error))

