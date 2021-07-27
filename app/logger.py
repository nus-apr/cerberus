# -*- coding: utf-8 -*-

import time
import datetime
import os
from app import definitions, values
from shutil import copyfile


def create():
    log_file_name = "log-" + str(time.time())
    log_file_path = definitions.DIRECTORY_LOG_BASE + "/" + log_file_name
    definitions.FILE_MAIN_LOG = log_file_path
    with open(definitions.FILE_MAIN_LOG, 'w+') as log_file:
        log_file.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")
    if os.path.exists(definitions.FILE_LAST_LOG):
        os.remove(definitions.FILE_LAST_LOG)
    if os.path.exists(definitions.FILE_ERROR_LOG):
        os.remove(definitions.FILE_ERROR_LOG)
    if os.path.exists(definitions.FILE_COMMAND_LOG):
        os.remove(definitions.FILE_COMMAND_LOG)
    if os.path.exists(definitions.FILE_ANALYSIS_LOG):
        os.remove(definitions.FILE_ANALYSIS_LOG)
    with open(definitions.FILE_LAST_LOG, 'w+') as last_log:
        last_log.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")
    with open(definitions.FILE_ERROR_LOG, 'w+') as error_log:
        error_log.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")
    with open(definitions.FILE_COMMAND_LOG, 'w+') as command_log:
        command_log.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")
    with open(definitions.FILE_ANALYSIS_LOG, 'w+') as analysis_log:
        command_log.write("[Start] " + values.TOOL_NAME + " started at " + str(datetime.datetime.now()) + "\n")


def log(log_message):
    log_message = "[" + str(time.asctime()) + "]" + log_message
    if "COMMAND" in log_message:
        with open(definitions.FILE_COMMAND_LOG, 'a') as log_file:
            log_file.write(log_message)
    with open(definitions.FILE_MAIN_LOG, 'a') as log_file:
        log_file.write(log_message)
    with open(definitions.FILE_LAST_LOG, 'a') as log_file:
        log_file.write(log_message)


def information(message):
    message = str(message).strip()
    message = "[INFO]: " + str(message) + "\n"
    log(message)


def trace(function_name, arguments):
    message = "[TRACE]: " + function_name + ": " + str(arguments.keys()) + "\n"
    log(message)


def command(message):
    message = str(message).strip().replace("[command]", "")
    message = "[COMMAND]: " + str(message) + "\n"
    log(message)


def data(message, data=None, is_patch=False):
    if values.DEBUG or is_patch:
        message = str(message).strip()
        message = "[DATA]: " + str(message) + "\n"
        log(message)
        if data:
            data = "[DATA]: " + str(data) + "\n"
            log(data)


def debug(message):
    message = str(message).strip()
    message = "[DEBUG]: " + str(message) + "\n"
    log(message)


def error(message):
    with open(definitions.FILE_ERROR_LOG, 'a') as last_log:
        last_log.write(str(message) + "\n")
    message = str(message).strip().lower().replace("[error]", "")
    message = "[ERROR]: " + str(message) + "\n"
    log(message)


def note(message):
    message = str(message).strip().lower().replace("[note]", "")
    message = "[NOTE]: " + str(message) + "\n"
    log(message)


def configuration(message):
    message = str(message).strip().lower().replace("[config]", "")
    message = "[CONFIGURATION]: " + str(message) + "\n"
    log(message)


def output(message):
    message = str(message).strip()
    message = "[LOG]: " + message
    log(message + "\n")


def warning(message):
    message = str(message).strip().lower().replace("[warning]", "")
    message = "[WARNING]: " + str(message) + "\n"
    log(message)


def analysis(exp_id):
    size_space, n_enumerated, n_plausible, n_noncompile = values.ANALYSIS_RESULTS[exp_id]
    n_implausible = n_enumerated - n_plausible - n_noncompile
    with open(definitions.FILE_ANALYSIS_LOG, 'a') as log_file:
        log_file.write(exp_id)
        log_file.write("\t\t\t\t search space size: {0]".format(size_space))
        log_file.write("\t\t\t\t count enumerations: {0]".format(n_enumerated))
        log_file.write("\t\t\t\t count plausible patches: {0]".format(n_plausible))
        log_file.write("\t\t\t\t count non-compiling patches: {0]".format(n_noncompile))
        log_file.write("\t\t\t\t count implausible patches: {0]".format(n_implausible))



def end(time_duration, is_error=False):
    output("\nTime duration\n----------------------\n\n")
    output("Iteration Count: " + str(values.ITERATION_NO))
    # # output("Patch Gen Count: " + str(values.COUNT_PATCH_GEN))
    # output("Patch Explored Count: " + str(values.COUNT_PATCHES_EXPLORED))
    # output("Patch Start Count: " + str(values.COUNT_PATCH_START))
    # output("Patch End Seed Count: " + str(values.COUNT_PATCH_END_SEED))
    # output("Patch End Count: " + str(values.COUNT_PATCH_END))
    # if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
    #     # output("Template Gen Count: " + str(values.COUNT_TEMPLATE_GEN))
    #     output("Template Explored Count: " + str(values.COUNT_TEMPLATES_EXPLORED))
    #     output("Template Start Count: " + str(values.COUNT_TEMPLATE_START))
    #     output("Template End Seed Count: " + str(values.COUNT_TEMPLATE_END_SEED))
    #     output("Template End Count: " + str(values.COUNT_TEMPLATE_END))
    # output("Paths Detected: " + str(values.COUNT_PATHS_DETECTED))
    # output("Paths Explored: " + str(values.COUNT_PATHS_EXPLORED))
    # output("Paths Skipped: " + str(values.COUNT_PATHS_SKIPPED))
    # output("Paths Hit Patch Loc: " + str(values.COUNT_HIT_PATCH_LOC))
    # output("Paths Hit Observation Loc: " + str(values.COUNT_HIT_BUG_LOG))
    # output("Paths Hit Crash Loc: " + str(values.COUNT_HIT_CRASH_LOC))
    # output("Paths Crashed: " + str(values.COUNT_HIT_CRASH))
    # output("Component Count: " + str(values.COUNT_COMPONENTS))
    # output("Component Count Gen: " + str(values.COUNT_COMPONENTS_GEN))
    # output("Component Count Cust: " + str(values.COUNT_COMPONENTS_CUS))
    # output("Gen Limit: " + str(values.DEFAULT_GEN_SEARCH_LIMIT))
    # if is_error:
    #     output(values.TOOL_NAME + " exited with an error after " + time_duration[
    #         definitions.KEY_DURATION_TOTAL] + " minutes")
    # else:
    #     output(values.TOOL_NAME + " finished successfully after " + time_duration[
    #         definitions.KEY_DURATION_TOTAL] + " minutes")
    log("[END] " + values.TOOL_NAME + " ended at  " + str(datetime.datetime.now()) + "\n\n")


