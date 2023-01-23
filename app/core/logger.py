# -*- coding: utf-8 -*-

import logging
import os
import time
from shutil import copyfile

from app.core import values

_logger_error: logging
_logger_command: logging
_logger_main: logging
_logger_build: logging


def setup_logger(name, log_file, level=logging.INFO, formatter=None):
    """To setup as many loggers as you want"""
    if formatter is None:
        formatter = logging.Formatter("%(asctime)s %(levelname)s %(message)s")
    handler = logging.FileHandler(log_file)
    handler.setFormatter(formatter)
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.addHandler(handler)
    return logger


def create_log_files():
    global _logger_main, _logger_build, _logger_command, _logger_error
    log_file_name = "log-" + str(time.time())
    log_file_path = values.dir_log_base + "/" + log_file_name
    values.file_main_log = log_file_path
    _logger_main = setup_logger("main", values.file_main_log, level=logging.DEBUG)
    _logger_error = setup_logger("error", values.file_error_log)
    _logger_command = setup_logger("command", values.file_command_log)
    _logger_build = setup_logger("build", values.file_build_log)


def store_log_file(log_file_path):
    if os.path.isfile(log_file_path):
        copyfile(log_file_path, values.dir_logs + "/" + log_file_path.split("/")[-1])


def store_logs():
    if os.path.isfile(values.file_main_log):
        copyfile(values.file_main_log, values.dir_logs + "/log-latest")
    log_file_list = [
        values.file_command_log,
        values.file_build_log,
        values.file_main_log,
        values.file_analysis_log,
        values.file_error_log,
    ]
    for log_f in log_file_list:
        store_log_file(log_f)


def build(message):
    _logger_build.info(message)


def information(message):
    _logger_main.info(message)


def command(message):
    message = str(message).strip().replace("[command]", "")
    message = "[COMMAND]: " + str(message) + "\n"
    _logger_main.info(message)
    _logger_command.info(message)


def docker_command(message):
    message = str(message).strip().replace("[command]", "")
    message = "[DOCKER-COMMAND]: " + str(message) + "\n"
    _logger_main.info(message)
    _logger_command.info(message)


def data(message):
    _logger_main.info(message)


def debug(message):
    message = str(message).strip()
    _logger_main.debug(message)


def error(message):
    _logger_main.error(message)
    _logger_error.error(message)


def note(message):
    _logger_main.info(message)


def configuration(message):
    message = str(message).strip().lower().replace("[config]", "")
    message = "[CONFIGURATION]: " + str(message) + "\n"
    _logger_main.info(message)


def output(message):
    message = str(message).strip()
    message = "[OUTPUT]: " + message
    _logger_main.info(message)


def warning(message):
    message = str(message).strip().lower().replace("[warning]", "")
    _logger_main.warning(message)


def analysis(exp_id):
    space_info, time_info = values.analysis_results[exp_id]
    with open(values.file_analysis_log, "a") as log_file:
        log_file.write("\n" + exp_id + "\n")
        log_file.write("\t\t search space size: {0}".format(space_info.size))
        log_file.write("\t\t count enumerations: {0}".format(space_info.enumerations))
        log_file.write("\t\t count plausible patches: {0}".format(space_info.plausible))
        log_file.write("\t\t count generated: {0}".format(space_info.generated))
        log_file.write(
            "\t\t count non-compiling patches: {0}".format(space_info.non_compilable)
        )
        log_file.write(
            "\t\t count implausible patches: {0}".format(space_info.get_implausible())
        )
        log_file.write("\t\t time build: {0} seconds".format(time_info.total_build))
        log_file.write(
            "\t\t time validation: {0} seconds".format(time_info.total_validation)
        )
        log_file.write(
            "\t\t time duration: {0} seconds".format(time_info.get_duration())
        )
        log_file.write(
            "\t\t latency compilation: {0} seconds".format(
                time_info.get_latency_compilation()
            )
        )
        log_file.write(
            "\t\t latency validation: {0} seconds".format(
                time_info.get_latency_validation()
            )
        )
        log_file.write(
            "\t\t latency plausible: {0} seconds".format(
                time_info.get_latency_plausible()
            )
        )
