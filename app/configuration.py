import os
import sys
import json
from app import definitions, values, emitter, utilities
from app.tools import Angelix, CPR, F1X, GenProg, Prophet, Fix2Fit
from app.benchmarks import ManyBugs


def read_arg(argument_list):
    emitter.normal("reading configuration values")
    if len(argument_list) > 0:
        for arg in argument_list:
            if definitions.ARG_DATA_PATH in arg:
                values.CONF_DATA_PATH = str(arg).replace(definitions.ARG_DATA_PATH, "")
            elif definitions.ARG_TOOL_NAME in arg:
                values.CONF_TOOL_NAME = str(arg).replace(definitions.ARG_TOOL_NAME, "").lower()
            elif definitions.ARG_SUBJECT_NAME in arg:
                values.CONF_SUBJECT_NAME = str(arg).replace(definitions.ARG_SUBJECT_NAME, "").lower()
            elif definitions.ARG_TOOL_PATH in arg:
                values.CONF_TOOL_PATH = str(arg).replace(definitions.ARG_TOOL_PATH, "")
            elif definitions.ARG_TOOL_PARAMS in arg:
                values.CONF_TOOL_PARAMS = str(arg).replace(definitions.ARG_TOOL_PARAMS, "")
            elif definitions.ARG_DEBUG_MODE in arg:
                values.CONF_DEBUG = True
            elif definitions.ARG_RUN_TESTS_ONLY in arg:
                values.CONF_RUN_TESTS_ONLY = True
            elif definitions.ARG_PURGE in arg:
                values.CONF_PURGE = True
            elif definitions.ARG_ANALYSE_ONLY in arg:
                values.CONF_ANALYSE_ONLY = True
            elif definitions.ARG_ONLY_SETUP in arg:
                values.CONF_SETUP_ONLY = True
            elif definitions.ARG_CONFIG_ID_LIST in arg:
                values.CONF_CONFIG_ID_LIST = str(arg).replace(definitions.ARG_CONFIG_ID_LIST, "").split(",")
            elif definitions.ARG_BUG_ID in arg:
                values.CONF_BUG_ID = int(str(arg).replace(definitions.ARG_BUG_ID, ""))
            elif definitions.ARG_START_ID in arg:
                values.CONF_START_ID = int(str(arg).replace(definitions.ARG_START_ID, ""))
            elif definitions.ARG_END_ID in arg:
                values.CONF_END_ID = int(str(arg).replace(definitions.ARG_END_ID, ""))
            elif definitions.ARG_BENCHMARK in arg:
                values.CONF_BENCHMARK = str(arg).replace(definitions.ARG_BENCHMARK, "")
            elif definitions.ARG_SKIP_LIST in arg:
                values.CONF_SKIP_LIST = str(arg).replace(definitions.ARG_SKIP_LIST, "").split(",")
            elif definitions.ARG_BUG_ID_LIST in arg:
                values.CONF_BUG_ID_LIST = str(arg).replace(definitions.ARG_BUG_ID_LIST, "").split(",")
            elif arg in ["--help", "-help", "-h"]:
                emitter.emit_help()
                exit(0)
            else:
                emitter.error("Unknown option: " + str(arg))
                emitter.emit_help()
                exit(1)
    if not values.CONF_SETUP_ONLY:
        if values.CONF_TOOL_NAME is None:
            emitter.error("[invalid] --tool is missing")
            emitter.emit_help()
            exit(1)
    if values.CONF_SUBJECT_NAME:
        emitter.normal("[info] running experiments for subject " + str(values.CONF_SUBJECT_NAME))
    if values.CONF_START_ID is None and values.CONF_BUG_ID is None and values.CONF_BUG_ID_LIST is None and values.CONF_SUBJECT_NAME is None:
        emitter.warning("[warning] experiment id is not specified, running all experiments")
    if values.CONF_BENCHMARK is None:
        emitter.error("[invalid] --benchmark is missing")
        emitter.emit_help()
        exit(1)
    else:
        values.FILE_META_DATA = "benchmark/" + values.CONF_BENCHMARK + "/meta-data.json"


def load_configuration_details(config_file_path):
    emitter.normal("loading configuration setup")
    json_data = None
    if os.path.isfile(config_file_path):
        with open(config_file_path, 'r') as conf_file:
            json_data = json.load(conf_file)
    else:
        utilities.error_exit("Configuration file does not exist")
    return json_data


def load_tool(tool_name):
    emitter.normal("loading repair tool")
    if tool_name == "cpr":
        return CPR.CPR()
    elif tool_name == "angelix":
        return Angelix.Angelix()
    elif tool_name == "prophet":
        return Prophet.Prophet()
    elif tool_name == "fix2fit":
        return Fix2Fit.Fix2Fit()
    elif tool_name == "f1x":
        return F1X.F1X()
    elif tool_name == "genprog":
        return GenProg.GenProg()
    else:
        utilities.error_exit("Unknown tool name", tool_name)


def load_benchmark(benchmark_name):
    emitter.normal("loading benchmark")
    if benchmark_name == "manybugs":
        return ManyBugs.ManyBugs()
    else:
        utilities.error_exit("Unknown benchmark name", benchmark_name)


def update_configuration():
    emitter.normal("updating configuration values")
    if values.CONF_RUN_TESTS_ONLY:
        values.DEFAULT_RUN_TESTS_ONLY = True
        values.DEFAULT_SETUP_ONLY = True
    if values.CONF_SETUP_ONLY:
        values.DEFAULT_SETUP_ONLY = True
    if values.CONF_ANALYSE_ONLY:
        values.DEFAULT_ANALYSE_ONLY = True
    sys.setrecursionlimit(values.DEFAULT_STACK_SIZE)

