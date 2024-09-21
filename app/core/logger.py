# -*- coding: utf-8 -*-
import logging
import os
import time
from logging import Formatter
from logging import Logger
from os.path import join
from shutil import copyfile
from typing import Any
from typing import Optional

from app.core import values
from app.core.task.stats.BenchmarkStats import BenchmarkStats
from app.core.task.stats.ToolStats import ToolStats

_logger_error: Logger
_logger_command: Logger
_logger_main: Logger
_logger_build: Logger


def setup_logger(
    name: Optional[str],
    log_file: str,
    level: int = logging.INFO,
    formatter: Optional[Formatter] = None,
) -> Logger:
    """To setup as many loggers as you want"""
    if formatter is None:
        formatter = logging.Formatter("%(asctime)s %(levelname)s %(message)s")
    handler = logging.FileHandler(log_file)
    handler.setFormatter(formatter)
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.addHandler(handler)
    return logger


def create_log_files() -> None:
    global _logger_main, _logger_build, _logger_command, _logger_error
    log_file_name = "log-{}".format(time.strftime("%b_%d_%H_%M"))
    log_file_path = join(values.dir_log_base, log_file_name)
    values.file_main_log = log_file_path
    _logger_main = setup_logger("main", values.file_main_log, level=logging.DEBUG)
    _logger_error = setup_logger("error", values.file_error_log)
    _logger_command = setup_logger("command", values.file_command_log)
    _logger_build = setup_logger("build", values.file_build_log)


def store_log_file(log_file_path: str) -> None:
    if os.path.isfile(log_file_path):
        copyfile(log_file_path, join(values.dir_logs, log_file_path.split("/")[-1]))


def store_logs() -> None:
    if os.path.isfile(values.file_main_log):
        copyfile(values.file_main_log, join(values.dir_logs, "log-latest"))
    log_file_list = [
        values.file_command_log,
        values.file_build_log,
        values.file_main_log,
        values.file_stats_log,
        values.file_error_log,
    ]
    for log_f in log_file_list:
        store_log_file(log_f)


def track_job(txt: Any) -> str:
    job = values.job_identifier.get("NAN")
    session = values.session_identifier.get("NAN")
    res = str(txt)
    if job != "NAN":
        res += job + "    " + str(txt)
    if session != "NAN":
        res += session + "    " + str(txt)
    return res


def build(message: Any) -> None:
    _logger_build.info(track_job(message))


def information(message: Any) -> None:
    _logger_main.info(track_job(message))


def command(message: Any) -> None:
    message = str(message).strip().replace("[command]", "")
    message = "[COMMAND]: {}\n".format(message)
    _logger_main.info(track_job(message))
    _logger_command.info(track_job(message))


def docker_command(message: Any) -> None:
    message = str(message).strip().replace("[command]", "")
    message = "[DOCKER-COMMAND]: {}\n".format(message)
    _logger_main.info(track_job(message))
    _logger_command.info(track_job(message))


def data(message: Any, info: Any) -> None:
    _logger_main.info(track_job(message), info)


def debug(message: Any) -> None:
    message = str(message).strip()
    _logger_main.debug(track_job(message))


def error(message: Any) -> None:
    _logger_main.error(track_job(message))
    _logger_error.error(track_job(message))


def note(message: Any) -> None:
    _logger_main.info(track_job(message))


def configuration(message: Any) -> None:
    message = str(message).strip().lower().replace("[config]", "")
    message = "[CONFIGURATION]: {}\n".format(message)
    _logger_main.info(track_job(message))


def output(message: Any) -> None:
    message = str(message).strip()
    message = "[OUTPUT]: {}".format(message)
    _logger_main.info(track_job(message))


def warning(message: Any) -> None:
    message = str(message).strip().lower().replace("[warning]", "")
    _logger_main.warning(track_job(message))


def log_tool_stats(task_tag_name: str, tool_stats: ToolStats) -> None:

    with open(values.file_stats_log, "a") as log_file:
        log_file.write("\nexperiment: {0}\n".format(task_tag_name))
        tool_stats.write(log_file.write, "\t\t")


def log_benchmark_stats(benchmark_tag: str, benchmark_stats: BenchmarkStats) -> None:

    with open(values.file_stats_log, "a") as log_file:
        log_file.write("\n benchmark bug: {0}\n".format(benchmark_tag))
        log_file.write("\t\t deployed: {0}\n".format(benchmark_stats.deployed))
        log_file.write("\t\t configured: {0}\n".format(benchmark_stats.configured))
        log_file.write("\t\t built: {0}\n".format(benchmark_stats.built))
        log_file.write("\t\t tested: {0}\n".format(benchmark_stats.tested))
