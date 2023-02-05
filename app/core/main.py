import argparse
import os
import signal
import time
import traceback
from multiprocessing import set_start_method

from app.core import (
    emitter,
    logger,
    definitions,
    values,
    configuration,
    repair,
    utilities,
)
from app.core.configuration import Configurations


def create_directories():
    dir_list = [
        values.dir_logs,
        values.dir_output_base,
        values.dir_log_base,
        values.dir_artifacts,
        values.dir_results,
        values.dir_experiments,
        values.dir_summaries
    ]

    for dir_i in dir_list:
        if not os.path.isdir(dir_i):
            os.makedirs(dir_i)


def timeout_handler(signum, frame):
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def shutdown(signum, frame):
    global stop_event
    emitter.warning("Exiting due to Terminate Signal")
    stop_event.set()
    raise SystemExit


def bootstrap(arg_list):
    emitter.sub_title("Bootstrapping framework")
    config = Configurations()
    config.read_arg_list(arg_list)
    values.arg_pass = True
    config.update_configuration()


def filter_experiment_list(benchmark):
    filtered_list = []
    experiment_list = benchmark.get_list()
    for bug_index in range(1, benchmark.size + 1):
        experiment_item = experiment_list[bug_index - 1]
        subject_name = experiment_item[definitions.KEY_SUBJECT]
        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        if values.bug_id_list and str(bug_name) not in values.bug_id_list:
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


def parse_args():
    parser = argparse.ArgumentParser(prog=values.tool_name, usage="%(prog)s [options]")
    parser._action_groups.pop()
    required = parser.add_argument_group("Required arguments")
    required.add_argument(
        "-b",
        definitions.ARG_BENCHMARK,
        help="repair benchmark",
        required=True,
        choices=values.get_list_benchmarks(),
    )

    optional = parser.add_argument_group("Optional arguments")
    optional.add_argument(
        "-d",
        definitions.ARG_DEBUG_MODE,
        help="print debugging information",
        action="store_true",
        default=False,
    )
    optional.add_argument(
        "-c",
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
        "--profile-list",
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
        type=list,
        nargs="+",
        default=[],
    )
    optional.add_argument("--config", help="configuration profile")

    args = parser.parse_args()
    return args


def run(repair_tool_list, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight(
        "[profile] repair-tool(s): " + " ".join([x.name for x in repair_tool_list])
    )
    emitter.highlight("[profile] repair-benchmark: " + benchmark.name)
    run_profile_id_list = values.profile_id_list
    iteration = 0
    for profile_id in run_profile_id_list:
        if profile_id not in setup:
            utilities.error_exit("invalid profile id " + profile_id)
        config_info = setup[profile_id]
        values.current_profile_id = config_info[definitions.KEY_ID]
        experiment_list = filter_experiment_list(benchmark)
        for experiment_item in experiment_list:
            iteration = iteration + 1
            values.ITERATION_NO = iteration
            bug_index = experiment_item[definitions.KEY_ID]
            emitter.sub_sub_title(
                "Experiment #" + str(iteration) + " - Bug #" + str(bug_index)
            )
            utilities.check_space()
            repair.run(benchmark, repair_tool_list, experiment_item, config_info)


def initialize():
    emitter.sub_title("Initializing setup")
    tool_list = []
    if values.tool_list:
        for tool_name in values.tool_list:
            tool = configuration.load_tool(tool_name)
            if not values.only_analyse:
                tool.check_tool_exists()
            tool_list.append(tool)
    benchmark = configuration.load_benchmark(values.benchmark_name.lower())
    setup = configuration.load_configuration_details(values.file_configuration)
    return tool_list, benchmark, setup


def main():
    parsed_args = parse_args()
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    set_start_method("spawn")
    start_time = time.time()
    create_directories()
    logger.create_log_files()
    try:
        emitter.title("Starting " + values.tool_name + " (Program Repair Framework) ")
        bootstrap(parsed_args)
        repair_tool_list, benchmark, setup = initialize()
        run(repair_tool_list, benchmark, setup)
    except SystemExit as e:
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
    except KeyboardInterrupt as e:
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
    except Exception as e:
        is_error = True
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
