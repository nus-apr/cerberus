import sys
import json
import subprocess
import os
import shutil
import traceback
import signal
import time
from app import emitter, logger, definitions, values, utilities, configuration
from app.benchmarks import AbstractBenchmark
from app.tools import AbstractTool
from os.path import dirname, abspath

start_time = 0
end_time = 0


def create_directories():
    if not os.path.isdir(definitions.DIR_LOGS):
        os.makedirs(definitions.DIR_LOGS)
    if not os.path.isdir(definitions.DIR_RESULT):
        os.makedirs(definitions.DIR_RESULT)
    if not os.path.isdir(definitions.DIRECTORY_LOG_BASE):
        os.makedirs(definitions.DIRECTORY_LOG_BASE)


def archive_results(dir_results):
    if not os.path.isdir(dir_results):
        os.makedirs(dir_results)
    experiment_id = dir_results.split("/")[-1]
    archive_command = "cd " + dirname(abspath(dir_results)) + "; tar cvzf " + experiment_id + ".tar.gz " + experiment_id
    utilities.execute_command(archive_command)


def repair(dir_expr, dir_setup, experiment_info, tool: AbstractTool, config_info):
    emitter.normal("\t\trepairing experiment subject")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_number = str(experiment_info[definitions.KEY_FIX_LINE])
    passing_test_list = experiment_info[definitions.KEY_PASSING_TEST].split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    timeout = int(config_info[definitions.KEY_CONFIG_TIMEOUT])
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    passing_test_list = passing_test_list[:int(len(passing_test_list) * test_ratio)]
    binary_input_arg = experiment_info[definitions.KEY_CRASH_CMD]
    subject_name = experiment_info[definitions.KEY_SUBJECT]
    fix_location = None
    binary_path = experiment_info[definitions.KEY_BINARY_PATH]
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + fix_line_number
    additional_tool_param = values.CONF_TOOL_PARAMS
    dir_logs = values.DIR_LOGS
    dir_results = values.DIR_RESULT
    utilities.check_space()
    tool.pre_process()
    tool.instrument(dir_logs, dir_expr, dir_setup, bug_id)
    tool.repair(values.DIR_LOGS, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
                failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg)
    tool.save_artefacts(dir_results, dir_expr, dir_setup, bug_id)
    tool.post_process(dir_expr, dir_results)


def run(repair_tool, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight("[configuration] repair-tool: " + repair_tool.name)
    emitter.highlight("[configuration] repair-benchmark: " + benchmark.name)
    run_config_id_list = values.CONF_CONFIG_ID_LIST
    for config_id in run_config_id_list:
        if config_id not in setup:
            utilities.error_exit("invalid configuration id " + config_id)
        config_info = setup[config_id]
        emitter.sub_sub_title("Configuration: " + config_info[definitions.KEY_ID])
        emitter.highlight("\t[configuration] timeout:" + str(config_info[definitions.KEY_ID]))
        emitter.highlight("\t[configuration] fix-loc: " + config_info[definitions.KEY_CONFIG_FIX_LOC])
        emitter.highlight("\t[configuration] test-suite ratio:" + str(config_info[definitions.KEY_CONFIG_TEST_RATIO]))
        experiment_list = benchmark.get_list()
        iteration = 0
        for index in range(1, benchmark.size):
            iteration = iteration + 1
            values.ITERATION_NO = iteration
            experiment_item = experiment_list[index - 1]
            subject_name = experiment_item[definitions.KEY_SUBJECT]
            if values.CONF_BUG_ID and index != values.CONF_BUG_ID:
                continue
            if values.CONF_BUG_ID_LIST and str(index) not in values.CONF_BUG_ID_LIST:
                continue
            if values.CONF_SKIP_LIST and str(index) in values.CONF_SKIP_LIST:
                continue
            if values.CONF_START_ID and index < values.CONF_START_ID:
                continue
            if values.CONF_END_ID and index > values.CONF_END_ID:
                break
            if values.CONF_SUBJECT_NAME and values.CONF_SUBJECT_NAME != subject_name:
                continue

            emitter.normal("Experiment-" + str(index))
            bug_name = str(experiment_item[definitions.KEY_BUG_ID])
            subject_name = str(experiment_item[definitions.KEY_SUBJECT])
            directory_name = benchmark.name + "/" + subject_name + "/" + bug_name
            dir_setup = definitions.DIR_MAIN + "/benchmark/" + directory_name
            dir_exp = values.CONF_DATA_PATH + "/" + directory_name + "/"
            tool_inst_dir = dir_setup + "/" + str(repair_tool.name).lower()

            emitter.normal("\t[META-DATA] project: " + subject_name)
            emitter.normal("\t[META-DATA] bug ID: " + bug_name)
            emitter.normal("\t[INFO] experiment directory: " + dir_exp)

            if not os.path.isdir(tool_inst_dir):
                emitter.warning("\t[warning] instrumentation not exist for tool, skipping experiment")
                continue
            dir_result = definitions.DIR_RESULT + "/" + "-".join([config_id, benchmark.name,
                                                                  repair_tool.name,
                                                                  subject_name, bug_name])
            benchmark.setup(index)
            benchmark.save_artefacts(dir_result, dir_exp)
            if not values.CONF_SETUP_ONLY:
                utilities.clean_results(dir_result)
                repair(dir_exp, dir_setup, experiment_item, repair_tool, config_info)
                archive_results(dir_result)
                if values.CONF_PURGE:
                    benchmark.clean(dir_exp)


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


def initialize():
    emitter.sub_title("Initializing setup")
    tool = configuration.load_tool(values.CONF_TOOL_NAME.lower())
    benchmark = configuration.load_benchmark(values.CONF_BENCHMARK.lower())
    setup = configuration.load_configuration_details(definitions.FILE_CONFIGURATION)
    return tool, benchmark, setup


def main():
    import sys
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    start_time = time.time()
    create_directories()
    logger.create()
    try:
        emitter.title("Starting " + values.TOOL_NAME + " (Program Repair Framework) ")
        bootstrap(sys.argv[1:])
        repair_tool, benchmark, setup = initialize()
        run(repair_tool, benchmark, setup)
    except SystemExit as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
        emitter.end(total_duration, is_error)
        logger.end(total_duration, is_error)
    except KeyboardInterrupt as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
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
        total_duration = format((time.time() - start_time) / 60, '.3f')
        emitter.end(total_duration, is_error)
        logger.end(total_duration, is_error)

