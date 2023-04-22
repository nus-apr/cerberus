import argparse
import multiprocessing
import os
import signal
import sys
import time
import traceback
from argparse import Namespace
from multiprocessing import set_start_method
from typing import Any
from typing import List

import rich.traceback
from rich import get_console

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import utilities
from app.core import values
from app.core.configuration import Configurations
from app.core.task import task
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.notification import notification
from app.ui import ui


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
    config.read_email_config_file()
    config.read_slack_config_file()
    config.read_arg_list(arg_list)
    values.arg_pass = True
    config.update_configuration()
    config.print_configuration()


def parse_args():
    parser = argparse.ArgumentParser(prog=values.tool_name, usage="%(prog)s [options]")
    parser._action_groups.pop()
    required = parser.add_argument_group("Required arguments")
    required.add_argument(
        "task_type",
        help="type of task to run",
        choices=["analyze", "prepare", "repair"],
    )

    optional = parser.add_argument_group("Optional arguments")
    optional.add_argument(
        "-c",
        definitions.ARG_CONFIG_FILE,
        help="configuration file",
        type=argparse.FileType("r"),
    )

    optional.add_argument(
        "-g",
        definitions.ARG_PARALLEL,
        help="Activate Textual UI",
        action="store_true",
        default=False,
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
        help="name of the repair/analysis tool",
        choices=values.get_list_tools(),
        metavar="TOOL",
    )

    # TODO: Group list of tools based on type
    # group_tool = parser.add_argument_group(title='choice of tools')
    # repair_tools = parser.add_argument_group(title='repair tools')
    # analysis_tools = parser.add_argument_group(title='analysis tools')
    #
    # group_tool.add_argument(repair_tools)
    # group_tool.add_argument(analysis_tools)
    #
    # group.add_argument('bacon', help="Lovely bacon", action='none')
    # group.add_argument('egg', help="The runny kind", action='none')
    # group.add_argument('sausage', help="Just a roll", action='none')
    # group.add_argument('spam', help="Glorious SPAM", action='none')
    # group.add_argument('tomato', help="Sliced and diced", action='none')

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
        nargs="+",
        help="list of the repair/analysis tool",
        choices=values.get_list_tools(),
    )
    optional.add_argument(
        definitions.ARG_REBUILD_ALL_IMAGES,
        help="rebuild all images",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        definitions.ARG_COMPACT_RESUTLS,
        help="compact results of runs - deletes artifacts after compressing",
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
        definitions.ARG_REPAIR_PROFILE_ID_LIST,
        help="multiple list of repair configuration profiles",
        dest="repair_profile_id_list",
        nargs="+",
        default=[],
    )

    optional.add_argument(
        definitions.ARG_CONTAINER_PROFILE_ID_LIST,
        help="multiple list of container configuration profiles",
        dest="container_profile_id_list",
        nargs="+",
        default=[],
    )

    optional.add_argument(
        definitions.ARG_RUNS,
        help="number of runs for an experiment",
        type=int,
        default=1,
    )

    optional.add_argument(
        definitions.ARG_CPU_COUNT,
        help="max amount of CPU cores which can be used by Cerberus",
        type=int,
        default=multiprocessing.cpu_count(),
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


def run(
    tool_list: List[AbstractTool],
    benchmark: AbstractBenchmark,
    repair_setup: Any,
    container_setup: Any,
):
    emitter.sub_title(f"Running {values.task_type} task")
    iteration = 0

    for repair_config_info in map(
        lambda repair_profile_id: repair_setup[repair_profile_id],
        values.repair_profile_id_list,
    ):

        for container_config_info in map(
            lambda container_profile_id: container_setup[container_profile_id],
            values.container_profile_id_list,
        ):

            values.current_repair_profile_id.set(repair_config_info[definitions.KEY_ID])
            values.current_container_profile_id.set(
                container_config_info[definitions.KEY_ID]
            )
            for experiment_item in filter_experiment_list(benchmark):
                bug_index = experiment_item[definitions.KEY_ID]
                cpu = ",".join(
                    map(
                        str,
                        range(
                            container_config_info.get(
                                definitions.KEY_CONTAINER_CPU_COUNT, values.cpus
                            )
                        ),
                    )
                )
                bug_name = str(experiment_item[definitions.KEY_BUG_ID])
                subject_name = str(experiment_item[definitions.KEY_SUBJECT])
                if values.use_container:
                    values.job_identifier.set(
                        "{}-{}-{}".format(benchmark.name, subject_name, bug_name)
                    )
                dir_info = task.generate_dir_info(
                    benchmark.name, subject_name, bug_name
                )
                benchmark.update_dir_info(dir_info)
                experiment_image_id = None
                if values.only_setup:
                    iteration = iteration + 1
                    values.iteration_no = iteration
                    emitter.sub_sub_title(
                        "Experiment #{} - Bug #{}".format(iteration, bug_index)
                    )
                    task.prepare(benchmark, experiment_item, cpu)
                    continue

                for tool in tool_list:
                    iteration = iteration + 1
                    values.iteration_no = iteration
                    emitter.sub_sub_title(
                        "Experiment #{} - Bug #{}".format(iteration, bug_index)
                    )
                    if experiment_image_id is None:
                        experiment_image_id = task.prepare(
                            benchmark, experiment_item, cpu
                        )
                    task.run(
                        benchmark,
                        tool,
                        experiment_item,
                        repair_config_info,
                        container_config_info,
                        str(bug_index),
                        cpu,
                        experiment_image_id,
                    )


def get_repair_setup() -> Any:
    emitter.normal("\t[framework] loading repair profile setup")
    repair_setup = configuration.load_configuration_details(
        values.file_repair_configuration
    )
    for repair_profile_id in values.repair_profile_id_list:
        if repair_profile_id not in repair_setup:
            utilities.error_exit(
                "invalid repair profile id {}".format(repair_profile_id)
            )
    return repair_setup


def get_container_setup() -> Any:
    emitter.normal("\t[framework] loading container profile setup")
    container_setup = configuration.load_configuration_details(
        values.file_container_configuration
    )
    for container_profile_id in values.container_profile_id_list:
        if container_profile_id not in container_setup:
            utilities.error_exit(
                "invalid container profile id {}".format(container_profile_id)
            )
    return container_setup


def get_tools() -> List[AbstractTool]:
    tool_list: List[AbstractTool] = []
    if values.task_type == "prepare":
        return tool_list
    for tool_name in values.tool_list:
        tool = configuration.load_tool(tool_name)
        if not values.only_analyse:
            tool.check_tool_exists()
        tool_list.append(tool)
    emitter.highlight(
        f"\t[framework] {values.task_type}-tool(s): "
        + " ".join([x.name for x in tool_list])
    )
    return tool_list


def get_benchmark() -> AbstractBenchmark:
    benchmark = configuration.load_benchmark(values.benchmark_name.lower())
    emitter.highlight(f"\t[framework] {values.task_type}-benchmark: {benchmark.name}")
    return benchmark


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
    if not sys.warnoptions:
        import warnings

        warnings.simplefilter("ignore")
    rich.traceback.install(show_locals=True)
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
        if parsed_args.parallel:
            info = sys.version_info
            if info.major < 3 or info.minor < 10:
                utilities.error_exit(
                    "Parallel mode is currently supported only for versions 3.10+"
                )
            ui.setup_ui()
        else:
            run(get_tools(), get_benchmark(), get_repair_setup(), get_container_setup())
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
        get_console().show_cursor(True)
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, ".3f")
        notification.end(total_duration, is_error)
        emitter.end(total_duration, is_error)
