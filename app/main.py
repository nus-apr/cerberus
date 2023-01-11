import os
import traceback
import signal
import time
from app import emitter, logger, definitions, values, utilities, configuration, repair
from multiprocessing import set_start_method


def create_directories():
    if not os.path.isdir(definitions.DIR_LOGS):
        os.makedirs(definitions.DIR_LOGS)
    if not os.path.isdir(definitions.DIR_ARTIFACTS):
        os.makedirs(definitions.DIR_ARTIFACTS)
    if not os.path.isdir(definitions.DIR_RESULT):
        os.makedirs(definitions.DIR_RESULT)
    if not os.path.isdir(definitions.DIR_EXPERIMENT):
        os.makedirs(definitions.DIR_EXPERIMENT)
    if not os.path.isdir(definitions.DIRECTORY_LOG_BASE):
        os.makedirs(definitions.DIRECTORY_LOG_BASE)


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
    configuration.read_arg(arg_list)
    values.CONF_ARG_PASS = True
    configuration.update_configuration()


def filter_experiment_list(benchmark):
    filtered_list = []
    experiment_list = benchmark.get_list()
    for bug_index in range(1, benchmark.size + 1):
        experiment_item = experiment_list[bug_index - 1]
        subject_name = experiment_item[definitions.KEY_SUBJECT]
        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        if values.CONF_BUG_ID and bug_name != values.CONF_BUG_ID:
            continue
        if values.CONF_BUG_ID_LIST and str(bug_name) not in values.CONF_BUG_ID_LIST:
            continue
        if values.CONF_BUG_INDEX and bug_index != values.CONF_BUG_INDEX:
            continue
        if (
            values.CONF_BUG_INDEX_LIST
            and int(bug_index) not in values.CONF_BUG_INDEX_LIST
        ):
            continue
        if values.CONF_SKIP_LIST and str(bug_index) in values.CONF_SKIP_LIST:
            continue
        if values.CONF_START_INDEX and bug_index < values.CONF_START_INDEX:
            continue
        if values.CONF_SUBJECT_NAME and values.CONF_SUBJECT_NAME != subject_name:
            continue
        if values.CONF_END_INDEX and bug_index > values.CONF_END_INDEX:
            break
        filtered_list.append(experiment_item)
    return filtered_list


def run(repair_tool_list, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight(
        "[profile] repair-tool(s): " + " ".join([x.name for x in repair_tool_list])
    )
    emitter.highlight("[profile] repair-benchmark: " + benchmark.name)
    run_config_id_list = values.CONF_CONFIG_ID_LIST
    iteration = 0
    for config_id in run_config_id_list:
        if config_id not in setup:
            utilities.error_exit("invalid profile id " + config_id)
        config_info = setup[config_id]
        values.CONFIG_ID = config_info[definitions.KEY_ID]
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
    if values.CONF_TOOL_LIST:
        for tool_name in values.CONF_TOOL_LIST:
            tool = configuration.load_tool(tool_name)
            if not values.DEFAULT_ANALYSE_ONLY:
                tool.check_tool_exists()
            tool_list.append(tool)
    elif values.CONF_TOOL_NAME:
        tool = configuration.load_tool(values.CONF_TOOL_NAME.lower())
        if not values.DEFAULT_ANALYSE_ONLY:
            tool.check_tool_exists()
        tool_list.append(tool)
    benchmark = configuration.load_benchmark(values.CONF_BENCHMARK.lower())
    setup = configuration.load_configuration_details(definitions.FILE_CONFIGURATION)
    return tool_list, benchmark, setup


def main():
    import sys

    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    set_start_method("spawn")
    start_time = time.time()
    create_directories()
    logger.create()
    try:
        emitter.title("Starting " + values.TOOL_NAME + " (Program Repair Framework) ")
        bootstrap(sys.argv[1:])
        repair_tool_list, benchmark, setup = initialize()
        run(repair_tool_list, benchmark, setup)
    except SystemExit as e:
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
        logger.end(total_duration, is_error)
    except KeyboardInterrupt as e:
        total_duration = format((time.time() - start_time) / 60, ".3f")
        emitter.end(total_duration, is_error)
        logger.end(total_duration, is_error)
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
        logger.end(total_duration, is_error)
