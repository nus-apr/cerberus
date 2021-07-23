import subprocess
import os
import sys
import signal
import random
from contextlib import contextmanager
from app import logger, emitter, values, definitions
import base64
import hashlib
import time



def execute_command(command, show_output=True):
    # Print executed command and execute it in console
    command = command.encode().decode('ascii', 'ignore')
    emitter.command(command)
    command = "{ " + command + " ;} 2> " + definitions.FILE_ERROR_LOG
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return int(process.returncode)


def error_exit(*arg_list):
    emitter.error("Repair Failed")
    for arg in arg_list:
        emitter.error(str(arg))
    raise Exception("Error. Exiting...")


def clean_files():
    # Remove other residual files stored in ./output/
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    emitter.information("Removing other residual files...")
    if os.path.isdir("output"):
        clean_command = "rm -rf " + definitions.DIRECTORY_OUTPUT
        execute_command(clean_command)


def backup_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    backup_command = "cp " + file_path + " " + definitions.DIRECTORY_BACKUP + "/" + backup_name
    execute_command(backup_command)


def restore_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    restore_command = "cp " + definitions.DIRECTORY_BACKUP + "/" + backup_name + " " + file_path
    execute_command(restore_command)


def reset_git(source_directory):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    reset_command = "cd " + source_directory + ";git reset --hard HEAD"
    execute_command(reset_command)


def build_clean(program_path):
    clean_command = "cd " + program_path + "; make clean; rm -rf klee-*"
    process = subprocess.Popen([clean_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    assert int(process.returncode) == 0
    return int(process.returncode)



@contextmanager
def timeout(time):
    signal.signal(signal.SIGALRM, raise_timeout)
    signal.alarm(time)

    try:
        yield
    except TimeoutError:
        pass
    finally:
        signal.signal(signal.SIGALRM, signal.SIG_IGN)


def raise_timeout(signum, frame):
    raise TimeoutError


def get_hash(str_value):
    str_encoded = str(str_value).encode('utf-8')
    str_hasher = hashlib.sha1(str_encoded)
    hash_value = base64.urlsafe_b64encode(str_hasher.digest()[:10])
    return hash_value


def create_directories():
    print("[DRIVER] Creating essential directory structure")
    if not os.path.isdir(DIR_LOGS):
        create_command = "mkdir " + DIR_LOGS
        execute_command(create_command)
    if not os.path.isdir(DIR_RESULT):
        create_command = "mkdir " + DIR_RESULT
        execute_command(create_command)
