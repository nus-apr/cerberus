import argparse
import os
import signal
import time
import traceback
from argparse import Namespace
from multiprocessing import set_start_method
from typing import Any
from typing import List
from typing import Tuple

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import repair
from app.core import ui
from app.core import utilities
from app.core import values
from app.core.configuration import Configurations
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


def create_output_directories():
    dir_list = [
        values.dir_logs,
        values.dir_output_base,
        values.dir_log_base,
        values.dir_artifacts,
        values.dir_results,
        values.dir_experiments,
        values.dir_summaries,
    ]

    for dir_i in dir_list:
        if not os.path.isdir(dir_i):
            os.makedirs(dir_i)


def timeout_handler(signum, frame):
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def shutdown(signum, frame):
    # global stop_event
    emitter.warning("Exiting due to Terminate Signal")
    # stop_event.set()
    raise SystemExit


def bootstrap(arg_list: Namespace):
    emitter.sub_title("Bootstrapping framework")
    config = Configurations()
    config.read_arg_list(arg_list)
    values.arg_pass = True
    config.update_configuration()
    config.print_configuration()


def parse_args():
    parser = argparse.ArgumentParser(prog=values.tool_name, usage="%(prog)s [options]")
    parser._action_groups.pop()
    # required = parser.add_argument_group("Required arguments")

    optional = parser.add_argument_group("Optional arguments")
    optional.add_argument(
        "-c",
        definitions.ARG_CONFIG_FILE,
        help="configuration file",
        type=argparse.FileType("r"),
    )

    optional.add_argument(
        "-e",
        definitions.ARG_EMAIL_CONFIG,
        help="email client configuration file",
        type=argparse.FileType("r"),
    )

    optional.add_argument(
        "-b",
        definitions.ARG_BENCHMARK,
        help="repair benchmark",
        choices=values.get_list_benchmarks(),
    )
    optional.add_argument(
        "-d",
        definitions.ARG_DEBUG_MODE,
        help="print debugging information",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_CACHE,
        help="use cached information for the process",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_BUG_INDEX, help="index of the bug in the benchmark", type=int
    )
    optional.add_argument(
        definitions.ARG_BUG_INDEX_LIST, help="list of bug indexes in the benchmark"
    )

    optional.add_argument(
        definitions.ARG_DOCKER_HOST,
        help="custom URL for the docker server which will host the containers",
    )

    optional.add_argument(
        "-t",
        definitions.ARG_TOOL_NAME,
        help="name of the repair tool",
        choices=values.get_list_tools(),
    )
    optional.add_argument(
        "-s",
        definitions.ARG_SUBJECT_NAME,
        help="filter the bugs using the subject name",
    )
    optional.add_argument(
        "-p", definitions.ARG_TOOL_PARAMS, help="pass parameters to the tool"
    )
    optional.add_argument(
        definitions.ARG_TOOL_LIST,
        help="list of repair tool names",
        nargs="+",
        default=[],
    )
    optional.add_argument(
        definitions.ARG_REBUILD_ALL_IMAGES,
        help="rebuild all images",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_REBUILD_BASE_IMAGE,
        help="rebuild the base images",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_PURGE,
        help="clean everything after the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_ANALYSE_ONLY,
        help="analyse the experiment",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_SETUP_ONLY,
        help="only setup the experiment",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_USE_CONTAINER,
        help="use containers for experiments",
        dest="use_container",
        action="store_true",
        default=True,
    )
    optional.add_argument(
        definitions.ARG_USE_LOCAL,
        help="use local machine for experiments",
        dest="use_local",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_DATA_PATH,
        help="directory path for data",
        dest="data_dir",
        action="store_true",
        default=False,
    )

    optional.add_argument(
        definitions.ARG_PROFILE_ID_LIST,
        help="multiple list of configuration profiles",
        dest="profile_id_list",
        nargs="+",
        default=[],
    )

    optional.add_argument(
        definitions.ARG_USE_GPU,
        help="allow gpu usage",
        action="store_true",
        default=False,
    )

    optional.add_argument(definitions.ARG_BUG_ID, help="identifier of the bug")
    optional.add_argument(
        definitions.ARG_BUG_ID_LIST,
        type=list,
        help="list of identifiers for the bugs",
        nargs="+",
        default=[],
    )
    optional.add_argument(
        definitions.ARG_START_INDEX,
        help="starting index for the list of bugs",
        type=int,
    )
    optional.add_argument(
        definitions.ARG_END_INDEX, help="ending index for the list of bugs", type=int
    )
    optional.add_argument(
        definitions.ARG_SKIP_LIST,
        help="list of bug index to skip",
        type=str,
        default="",
    )
    args = parser.parse_args()
    return args


def filter_experiment_list(benchmark: AbstractBenchmark):
    filtered_list = []
    experiment_list = benchmark.get_list()
    for bug_index in range(1, benchmark.size + 1):
        experiment_item = experiment_list[bug_index - 1]
        subject_name = experiment_item[definitions.KEY_SUBJECT]
        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        if values.bug_id_list and bug_name not in values.bug_id_list:
            continue
        if values.bug_index_list and bug_index not in values.bug_index_list:
            continue
        if values.skip_index_list and str(bug_index) in values.skip_index_list:
            continue
        if values.start_index and bug_index < values.start_index:
            continue
        if values.subject_name and values.subject_name != subject_name:
            continue
        if values.end_index and bug_index > values.end_index:
            break
        filtered_list.append(experiment_item)
    return filtered_list


def main():
    parsed_args = parse_args()
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    set_start_method("spawn")
    start_time = time.time()
    create_output_directories()
    logger.create_log_files()
    try:
        emitter.title("Starting " + values.tool_name + " (Program Repair Framework) ")
        bootstrap(parsed_args)
        ui.setup_ui()
    except (SystemExit, KeyboardInterrupt) as e:
        pass
    except Exception as e:
        is_error = True
        values.ui_active = False
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        values.ui_active = False
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
