import os
import sys
import json
from app import definitions, values, emitter, utilities

def convert_range(x):
    parts = x.split('-')
    if len(parts) == 1:
            return [int(parts[0])]
    if len(parts) == 0:
            return []
    parts[0] = 1 if parts[0] == '' else int(parts[0])
    parts[1] = 999 if parts[1] == '' else int(parts[1])
    return range(parts[0],parts[1]+1) 

flat_map = lambda f, xs: (y for ys in xs for y in f(ys))


def read_arg(argument_list):
    emitter.normal("reading profile values")
    if len(argument_list) > 0:
        for arg in argument_list:
            if definitions.ARG_DATA_PATH in arg:
                values.CONF_DATA_PATH = str(arg).replace(definitions.ARG_DATA_PATH, "")
            elif definitions.ARG_TOOL_NAME in arg:
                values.CONF_TOOL_NAME = str(arg).replace(definitions.ARG_TOOL_NAME, "").lower()
            elif definitions.ARG_TOOL_LIST in arg:
                values.CONF_TOOL_LIST = str(arg).replace(definitions.ARG_TOOL_LIST, "").lower().split(",")
            elif definitions.ARG_SUBJECT_NAME in arg:
                values.CONF_SUBJECT_NAME = str(arg).replace(definitions.ARG_SUBJECT_NAME, "").lower()
            elif definitions.ARG_TOOL_PATH in arg:
                values.CONF_TOOL_PATH = str(arg).replace(definitions.ARG_TOOL_PATH, "")
            elif definitions.ARG_TOOL_PARAMS in arg:
                values.CONF_TOOL_PARAMS = str(arg).replace(definitions.ARG_TOOL_PARAMS, "")
            elif definitions.ARG_DEBUG_MODE in arg:
                values.CONF_DEBUG = True
            elif definitions.ARG_VALIDATOR_THREADS in arg:
                values.CONF_USE_VTHREADS = True
            elif definitions.ARG_RUN_TESTS_ONLY in arg:
                values.CONF_RUN_TESTS_ONLY = True
            elif definitions.ARG_PURGE in arg:
                values.CONF_PURGE = True
            elif definitions.ARG_ANALYSE_ONLY in arg:
                values.CONF_ANALYSE_ONLY = True
            elif definitions.ARG_VALKYRIE in arg:
                values.CONF_USE_VALKYRIE = True
            elif definitions.ARG_ONLY_SETUP in arg:
                values.CONF_SETUP_ONLY = True
            elif definitions.ARG_USE_CONTAINER in arg:
                values.CONF_USE_CONTAINER = True
            elif definitions.ARG_USE_LOCAL in arg:
                values.CONF_USE_CONTAINER = False
            elif definitions.ARG_INSTRUMENT_ONLY in arg:
                values.CONF_INSTRUMENT_ONLY = True
            elif definitions.ARG_SHOW_DEV_PATCH in arg:
                values.CONF_SHOW_DEV_PATCH = True
            elif definitions.ARG_CONFIG_ID_LIST in arg:
                values.CONF_CONFIG_ID_LIST = str(arg).replace(definitions.ARG_CONFIG_ID_LIST, "").split(",")
            elif definitions.ARG_BUG_INDEX in arg:
                values.CONF_BUG_INDEX = int(str(arg).replace(definitions.ARG_BUG_INDEX, ""))
            elif definitions.ARG_BUG_ID in arg:
                values.CONF_BUG_ID = str(arg).replace(definitions.ARG_BUG_ID, "")
            elif definitions.ARG_DUMP_PATCHES in arg:
                values.CONF_DUMP_PATCHES = True
            elif definitions.ARG_START_INDEX in arg:
                values.CONF_START_INDEX = int(str(arg).replace(definitions.ARG_START_INDEX, ""))
            elif definitions.ARG_END_INDEX in arg:
                values.CONF_END_INDEX = int(str(arg).replace(definitions.ARG_END_INDEX, ""))
            elif definitions.ARG_BENCHMARK in arg:
                values.CONF_BENCHMARK = str(arg).replace(definitions.ARG_BENCHMARK, "")
            elif definitions.ARG_SKIP_LIST in arg:
                values.CONF_SKIP_LIST = str(arg).replace(definitions.ARG_SKIP_LIST, "").split(",")
            elif definitions.ARG_BUG_INDEX_LIST in arg:
                values.CONF_BUG_INDEX_LIST = list(flat_map(convert_range,str(arg).replace(definitions.ARG_BUG_INDEX_LIST, "").split(",")))
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
        if values.CONF_TOOL_NAME is None and not values.CONF_TOOL_LIST:
            emitter.error("[invalid] --tool/-tool-list is missing")
            emitter.emit_help()
            exit(1)
    if values.CONF_SUBJECT_NAME:
        emitter.normal("[info] running experiments for subject " + str(values.CONF_SUBJECT_NAME))
    if values.CONF_START_INDEX is None and values.CONF_BUG_INDEX is None and values.CONF_BUG_INDEX_LIST is None and values.CONF_SUBJECT_NAME is None:
        emitter.warning("[warning] experiment id is not specified, running all experiments")
    if values.CONF_BENCHMARK is None:
        emitter.error("[invalid] --benchmark is missing")
        emitter.emit_help()
        exit(1)
    else:
        values.FILE_META_DATA = "benchmark/" + values.CONF_BENCHMARK + "/meta-data.json"


def load_configuration_details(config_file_path):
    emitter.normal("loading profile setup")
    json_data = None
    if os.path.isfile(config_file_path):
        with open(config_file_path, 'r') as conf_file:
            json_data = json.load(conf_file)
    else:
        utilities.error_exit("Configuration file does not exist")
    return json_data

def load_class(class_name):
    components = class_name.split('.')
    mod = __import__(components[0])
    for comp in components[1:]:
        mod = getattr(mod, comp)
    return mod


def load_tool(tool_name):
    emitter.normal("loading repair tool")
    class_file_path = definitions.DIR_TOOL_DRIVERS + tool_name + ".py"
    existing_tool_list = os.listdir(definitions.DIR_TOOL_DRIVERS)
    tool_class_name = None
    for tool in existing_tool_list:
        if tool.lower().replace(".py", "") == tool_name.lower():
            tool_class_name = tool.replace(".py", "")
    if not tool_class_name:
        utilities.error_exit("Unknown tool name", tool_name)
    mod = __import__('app.tools', fromlist=[tool_class_name])
    tool_class = getattr(mod, str(tool_class_name))
    initializer = getattr(tool_class, str(tool_class_name))
    return initializer()


def load_benchmark(benchmark_name):
    emitter.normal("loading benchmark")
    class_file_path = definitions.DIR_BENCHMARK_DRIVERS + benchmark_name + ".py"
    existing_benchmark_list = os.listdir(definitions.DIR_BENCHMARK_DRIVERS)
    benchmark_class_name = None
    for benchmark in existing_benchmark_list:
        if benchmark.lower().replace(".py", "") == benchmark_name.lower():
            benchmark_class_name = benchmark.replace(".py", "")
    if not benchmark_class_name:
        utilities.error_exit("Unknown benchmark name", benchmark_name)
    mod = __import__('app.benchmarks', fromlist=[benchmark_class_name])
    benchmark_class = getattr(mod, str(benchmark_class_name))
    initializer = getattr(benchmark_class, str(benchmark_class_name))
    return initializer()


def update_configuration():
    emitter.normal("updating profile values")
    if values.CONF_RUN_TESTS_ONLY:
        values.DEFAULT_RUN_TESTS_ONLY = True
        values.DEFAULT_SETUP_ONLY = True
    if values.CONF_SETUP_ONLY:
        values.DEFAULT_SETUP_ONLY = True
    if values.CONF_ANALYSE_ONLY:
        values.DEFAULT_ANALYSE_ONLY = True
    if values.CONF_USE_CONTAINER:
        values.DEFAULT_USE_CONTAINER = True
    else:
        values.DEFAULT_USE_CONTAINER = False
    if values.CONF_DUMP_PATCHES:
        values.DEFAULT_DUMP_PATCHES = True
    if values.CONF_USE_VALKYRIE:
        values.DEFAULT_USE_VALKYRIE = True
        values.DEFAULT_DUMP_PATCHES = True
    if values.CONF_USE_VTHREADS:
        values.DEFAULT_USE_VTHREADS = True
    sys.setrecursionlimit(values.DEFAULT_STACK_SIZE)
