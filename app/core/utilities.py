import base64
import hashlib
import os
import re
import shutil
import signal
import subprocess
import sys
from contextlib import contextmanager
from os.path import abspath
from os.path import dirname
from os.path import join
from typing import Any
from typing import Callable
from typing import Dict
from typing import Generator
from typing import List
from typing import NoReturn
from typing import Optional
from typing import Tuple

from app.core import emitter
from app.core import logger
from app.core import values
from app.notification import notification


def escape_ansi(text: str) -> str:
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


def create_output_directories() -> None:
    dir_list = [
        values.dir_logs,
        values.dir_output_base,
        values.dir_log_base,
        values.dir_artifacts,
        values.dir_results,
        values.dir_experiments,
        values.dir_summaries,
        values.dir_summaries_tools,
        values.dir_summaries_benchmarks,
    ]

    for dir_i in dir_list:
        if not os.path.isdir(dir_i):
            os.makedirs(dir_i)


def execute_command(
    command: str,
    show_output: bool = True,
    env: Dict[str, str] = dict(),
    directory: Optional[str] = None,
) -> int:
    # Print executed command and execute it in console
    command = command.encode().decode("ascii", "ignore")
    if not directory:
        directory = os.getcwd()
        print_command = "[{}] {}".format(directory, command)
    else:
        print_command = "[{}] {}".format(directory, command)

    if env:
        print_command += f""" ({' '.join(f"{k}={v}" for k, v in env.items())})"""

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
    if output:
        emitter.debug(f"[execute-command][stdout] {output.decode('utf-8')}")
    if error:
        emitter.error(f"[execute-command][stderr] {error.decode('utf-8')}")
    # out is the output of the command, and err is the exit value
    return int(process.returncode)


def run_command(
    command: str,
    show_output: bool = True,
    env: Dict[str, str] = dict(),
    directory: Optional[str] = None,
) -> Tuple[int, Tuple[bytes, bytes]]:
    # Print executed command and execute it in console
    command = command.encode().decode("ascii", "ignore")
    if not directory:
        directory = os.getcwd()
        print_command = "[{}] {}".format(directory, command)
    else:
        print_command = "[{}] {}".format(directory, command)

    if env:
        print_command += f""" ({' '.join(f"{k}={v}" for k, v in env.items())})"""

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
    if output:
        emitter.debug(output.decode("utf-8"))
    if error:
        emitter.error(error.decode("utf-8"))
    # out is the output of the command, and err is the exit value
    return int(process.returncode), (output, error)


def error_exit(*arg_list: Any) -> NoReturn:
    emitter.error(f"Task {values.task_type.get()} failed")
    notification.error_exit()
    for arg in arg_list:
        emitter.error(str(arg))
    raise Exception(
        "Error{}. Exiting...".format(
            " for subject {}".format(values.job_identifier.get())
            if values.job_identifier.get(None)
            else ""
        )
    )


def get_gpu_count() -> int:
    """
    Get the number of gpus on the system. Uses nvidia-smi to obtain the number.
    """
    try:
        return len(
            subprocess.check_output(["nvidia-smi", "-L"])
            .decode("utf-8")
            .strip()
            .split("\n")
        )
    except:
        return 0


def flat_map(f: Callable[[Any], Any], xs: List[Any]) -> Generator[Any, None, None]:
    return (y for ys in xs for y in f(ys))


def clean_artifacts(output_dir: str) -> None:
    emitter.debug(f"[framework] cleaning artifacts at {output_dir}")
    if os.path.isdir(output_dir):
        execute_command("rm -rf {}".format(output_dir))
    execute_command("mkdir {}".format(output_dir))


def archive_results(dir_results: str, dir_archive: str) -> int:
    for output_dir in [dir_results, dir_archive]:
        if not os.path.isdir(output_dir):
            os.makedirs(output_dir)

    experiment_id = dir_results.split("/")[-1]

    archive_command = (
        "cd {res} ; tar cvzf {id}.tar.gz {id} ; mv {id}.tar.gz {arc}".format(
            res=dirname(abspath(dir_results)), id=experiment_id, arc=dir_archive
        )
    )

    return execute_command(archive_command)


@contextmanager
def timeout(time: int) -> Generator[None, None, None]:
    signal.signal(signal.SIGALRM, raise_timeout)
    signal.alarm(time)
    try:
        yield
    except TimeoutError:
        pass
    finally:
        signal.signal(signal.SIGALRM, signal.SIG_IGN)


def raise_timeout(signum: int, frame: Any) -> NoReturn:
    raise TimeoutError


def get_hash(str_value: str) -> bytes:
    str_encoded = str_value.encode("utf-8")
    str_hasher = hashlib.sha1(str_encoded)
    hash_value = base64.urlsafe_b64encode(str_hasher.digest()[:10])
    return hash_value


def check_space() -> None:
    emitter.normal("\t\t[framework] checking disk space")
    total, used, free = shutil.disk_usage("/")
    emitter.information("\t\t\t total: %d GiB" % (total // (2**30)))
    emitter.information("\t\t\t used: %d GiB" % (used // (2**30)))
    emitter.information("\t\t\t free: %d GiB" % (free // (2**30)))
    free_size = free // (2**30)
    if int(free_size) < values.default_disk_space:
        error_exit("\t\t\tinsufficient disk space " + str(free_size))
