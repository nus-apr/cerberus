import base64
import hashlib
import os
import re
import shutil
import signal
import subprocess
import sys
from contextlib import contextmanager
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import values


def escape_ansi(text):
    # 7-bit C1 ANSI sequences
    ansi_escape = re.compile(
        r"""
        \x1B  # ESC
        (?:   # 7-bit C1 Fe (except CSI)
            [@-Z\\-_]
        |     # or [ for CSI, followed by a control sequence
            \[
            [0-?]*  # Parameter bytes
            [ -/]*  # Intermediate bytes
            [@-~]   # Final byte
        )
    """,
        re.VERBOSE,
    )
    result = ansi_escape.sub("", text)
    return result


def execute_command(command, show_output=True, env=dict()):
    # Print executed command and execute it in console
    command = command.encode().decode("ascii", "ignore")
    emitter.command(command)
    command = "{ " + command + " ;} 2> " + values.file_error_log
    if not show_output:
        command += " > /dev/null"
    # print(command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True, env=env)
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
        clean_command = "rm -rf " + values.dir_output
        execute_command(clean_command)


def clean_artifacts(output_dir):
    if os.path.isdir(output_dir):
        rm_command = "rm -rf " + output_dir
        execute_command(rm_command)
    mk_command = "mkdir " + output_dir
    execute_command(mk_command)


def backup_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    backup_command = "cp {} {}".format(file_path, join(values.dir_backup, backup_name))
    execute_command(backup_command)


def restore_file(file_path, backup_name):
    logger.trace(__name__ + ":" + sys._getframe().f_code.co_name, locals())
    restore_command = "cp " + values.dir_backup + "/" + backup_name + " " + file_path
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
    str_encoded = str(str_value).encode("utf-8")
    str_hasher = hashlib.sha1(str_encoded)
    hash_value = base64.urlsafe_b64encode(str_hasher.digest()[:10])
    return hash_value


def check_space():
    emitter.normal("\t\t\t checking disk space")
    total, used, free = shutil.disk_usage("/")
    emitter.information("\t\t\t\t Total: %d GiB" % (total // (2**30)))
    emitter.information("\t\t\t\t Used: %d GiB" % (used // (2**30)))
    emitter.information("\t\t\t\t Free: %d GiB" % (free // (2**30)))
    free_size = free // (2**30)
    if int(free_size) < values.default_disk_space:
        error_exit("insufficient disk space " + str(free_size))
