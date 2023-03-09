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
from typing import Any

from app.core import definitions
from app.core import email
from app.core import emitter
from app.core import logger
from app.core import values


def escape_ansi(text: str):
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


def execute_command(command: str, show_output=True, env=dict(), directory=None):
    # Print executed command and execute it in console
    command = command.encode().decode("ascii", "ignore")
    if not directory:
        directory = os.getcwd()
        print_command = command
    else:
        print_command = "[{}] {}".format(directory, command)
    emitter.command(print_command)
    command = "{{ {} ;}} 2> {}".format(command, values.file_error_log)
    if not show_output:
        command += " > /dev/null"
    # print(command)
    new_env = os.environ.copy()
    new_env.update(env)
    process = subprocess.Popen(
        [command], stdout=subprocess.PIPE, shell=True, env=new_env, cwd=directory
    )
    (output, error) = process.communicate()
    # out is the output of the command, and err is the exit value
    return int(process.returncode)


def error_exit(*arg_list: Any):
    emitter.error("Repair Failed")
    if values.email_setup:
        email.send_message("\n".join(map(str, arg_list)), "Cerberus Repair Failed")
    for arg in arg_list:
        emitter.error(str(arg))
    raise Exception("Error. Exiting...")


def clean_files():
    # Remove other residual files stored in ./output/
    logger.trace("{}:{}".format(__name__, sys._getframe().f_code.co_name), locals())
    emitter.information("Removing other residual files...")
    if os.path.isdir("output"):
        clean_command = "rm -rf " + values.dir_output
        execute_command(clean_command)


def clean_artifacts(output_dir: str):
    if os.path.isdir(output_dir):
        execute_command("rm -rf {}".format(output_dir))
    execute_command("mkdir {}".format(output_dir))


def backup_file(file_path: str, backup_name: str):
    logger.trace("{}:{}".format(__name__, sys._getframe().f_code.co_name), locals())
    backup_command = "cp {} {}".format(file_path, join(values.dir_backup, backup_name))
    execute_command(backup_command)


def restore_file(file_path: str, backup_name: str):
    logger.trace("{}:{}".format(__name__, sys._getframe().f_code.co_name), locals())
    restore_command = "cp {} {}".format(join(values.dir_backup, backup_name), file_path)
    execute_command(restore_command)


def reset_git(source_directory: str):
    logger.trace("{}:{}".format(__name__, sys._getframe().f_code.co_name), locals())
    reset_command = "cd " + source_directory + ";git reset --hard HEAD"
    execute_command(reset_command)


def build_clean(program_path: str):
    clean_command = "cd " + program_path + "; make clean; rm -rf klee-*"
    process = subprocess.Popen([clean_command], stderr=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    assert int(process.returncode) == 0
    return int(process.returncode)


@contextmanager
def timeout(time: int):
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


def get_hash(str_value: str):
    str_encoded = str_value.encode("utf-8")
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
