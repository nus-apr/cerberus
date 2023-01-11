import argparse
import os
import signal
import time
import traceback
from multiprocessing import set_start_method

from app.core import emitter, logger, definitions, values, configuration, repair, utilities
from app.core.configuration import Configurations


def create_directories():
    dir_list = [
        values.dir_logs,
        values.dir_output_base,
        values.dir_log_base,
        values.dir_artifacts,
        values.dir_results,
        values.dir_experiments
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
    parser = argparse.ArgumentParser(prog=values.tool_name, usage='%(prog)s [options]')
    parser._action_groups.pop()
    required = parser.add_argument_group('required arguments')
    required.add_argument('-b', '--benchmark', help='repair benchmark', required=True,
                          choices = values.get_list_benchmarks()
                          )

    optional = parser.add_argument_group('optional arguments')
    optional.add_argument('-d', '--debug', help='print debugging information',
                          action='store_true',
                          default=False)
    optional.add_argument('-c', '--cache', help='use cached information for the process',
                          action='store_true',
                          default=False)

    optional.add_argument('--bug-index', help='index of the bug in the benchmark',
                          type=int)
    optional.add_argument('--bug-index-list', help='list of bug indexes in the benchmark',
                          action='store_true')

    optional.add_argument('-t', '--tool', help='name of the repair tool',
                          choices= values.get_list_tools()
                          )
    optional.add_argument('-s', '--subject', help='filter the bugs using the subject name')
    optional.add_argument('-p', '--tool-param', help='filter the bugs using the subject name')
    optional.add_argument('--tool-list', help='list of repair tool names')
    optional.add_argument('--rebuild-all', help='rebuild all images',
                          action='store_true', default=False)
    optional.add_argument('--rebuild-base', help='rebuild the base images',
                          action='store_true', default=False)
    optional.add_argument('--purge', help='clean everything after the experiment',
                          action='store_true', default=False)

    optional.add_argument('--only-analyse', help='analyse the previous run',
                          action='store_true', default=False)
    optional.add_argument('--only-setup', help='analyse the previous run',
                          action='store_true', default=False)
    optional.add_argument('--container', help='use containers for experiments', dest="use_container",
                          action='store_true', default=True)

    optional.add_argument('--local', help='use local machine for experiments', dest="use_local",
                          action='store_true', default=False)

    optional.add_argument('--dir-data', help='directory path for data', dest="data_dir",
                          action='store_true', default=False)

    optional.add_argument('--config-list', help='multiple list of configurations', dest="config_id_list",
                          action='store_true', default=False)

    optional.add_argument('--bug-id', help='identifier of the bug')
    optional.add_argument('--bug-id-list', type=list, help='list of identifiers for the bugs')
    optional.add_argument('--start-index', help='starting index for the list of bugs')
    optional.add_argument('--end-index', help='ending index for the list of bugs')
    optional.add_argument('--skip-index-list', help='list of bug index to skip', type=list)
    optional.add_argument('--config', help='configuration profile')

    args = parser.parse_args()
    return args


def run(repair_tool_list, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight(
        "[profile] repair-tool(s): " + " ".join([x.name for x in repair_tool_list])
    )
    emitter.highlight("[profile] repair-benchmark: " + benchmark.name)
    run_config_id_list = values.config_id_list
    iteration = 0
    for config_id in run_config_id_list:
        if config_id not in setup:
            utilities.error_exit("invalid profile id " + config_id)
        config_info = setup[config_id]
        values.config_id = config_info[definitions.KEY_ID]
        experiment_list = filter_experiment_list(benchmark)
        for experiment_item in experiment_list:
            iteration = iteration + 1
            values.ITERATION_NO = iteration
            bug_index = experiment_item[definitions.KEY_ID]
            emitter.sub_sub_title(
                "Experiment #" + str(iteration) + " - Bug #" + str(bug_index)
            )
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
