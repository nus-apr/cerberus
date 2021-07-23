import sys
import json
import subprocess
import os
import shutil
import signal
import time
from app import emitter, logger, definitions, values, utilities, configuration
from app.benchmarks import AbstractBenchmark
from app.tools import AbstractTool
from os.path import dirname, abspath

start_time = 0
end_time = 0


def create_directories():
    print("[Cerberus] creating essential directory structure")
    if not os.path.isdir(definitions.DIR_LOGS):
        create_command = "mkdir " + definitions.DIR_LOGS
        utilities.execute_command(create_command)
    if not os.path.isdir(definitions.DIR_RESULT):
        create_command = "mkdir " + definitions.DIR_RESULT
        utilities.execute_command(create_command)


def archive_results(benchmark: AbstractBenchmark, tool: AbstractTool, dir_results, dir_experiment):
    if not os.path.isdir(dir_results):
        os.makedirs(dir_results)
    benchmark.save_artefacts(dir_results, dir_experiment)
    tool.save_artefacts(dir_results, dir_experiment)
    experiment_id = dir_results.split("/")[-1]
    archive_command = "cd " + dirname(abspath(dir_results)) + "; tar cvzf " + experiment_id + ".tar.gz " + experiment_id
    utilities.execute_command(archive_command)


def repair(dir_expr, dir_setup, experiment_info, tool: AbstractTool):
    global CONF_TOOL_NAME, CONF_CONFIG_ID, FILE_CONFIGURATION, CONFIG_INFO, DIR_EXPERIMENT
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_number = str(experiment_info[definitions.KEY_FIX_LINE])
    passing_test_list = experiment_info[definitions.KEY_PASSING_TEST].split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    timeout = int(CONFIG_INFO[definitions.KEY_CONFIG_TIMEOUT])
    test_ratio = float(CONFIG_INFO[definitions.KEY_CONFIG_TEST_RATIO])
    passing_test_list = passing_test_list[:int(len(passing_test_list) * test_ratio)]
    binary_input_arg = experiment_info[definitions.KEY_CRASH_CMD]
    subject_name = experiment_info[definitions.KEY_SUBJECT]
    fix_location = None
    binary_path = experiment_info[definitions.KEY_BINARY_PATH]
    if CONFIG_INFO[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + fix_line_number
    additional_tool_param = values.CONF_TOOL_PARAMS
    dir_logs = values.DIR_LOGS
    dir_results = values.DIR_RESULT
    tool.pre_process()
    tool.instrument(dir_logs, dir_expr, dir_setup, bug_id)
    tool.repair(values.DIR_LOGS, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
                failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg)
    tool.save_artefacts(dir_results, dir_expr, dir_setup, bug_id)
    tool.post_process(dir_expr, dir_results)


def run(arg_list):
    print("[Cerberus] Running cerberus")
    configuration.read_arg(arg_list)
    create_directories()
    repair_tool = configuration.load_tool(values.CONF_TOOL_NAME.lower())
    benchmark = configuration.load_benchmark(values.CONF_BENCHMARK.lower())
    configuration_list = values.CONF_CONFIG_ID_LIST

    for config_id in configuration_list:
        config_info = configuration.load_configuration_details(definitions.FILE_CONFIGURATION, config_id)
        experiment_list = benchmark.experiment_list
        for index in range(1, benchmark.size):
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

            experiment_name = "\n\nConfiguration-" + str(config_id) + " : Experiment-" + str(index) + "\n-----------------------------"
            print(experiment_name)
            bug_name = str(experiment_item[definitions.KEY_BUG_ID])
            subject_name = str(experiment_item[definitions.KEY_SUBJECT])
            directory_name = values.CONF_BENCHMARK + "/" + subject_name + "/" + bug_name
            dir_setup = definitions.DIR_MAIN + "/benchmark/" + directory_name
            dir_exp = values.CONF_DATA_PATH + "/" + directory_name + "/"
            tool_inst_dir = dir_setup + "/" + str(CONF_TOOL_NAME).lower()

            print("\t[META-DATA] benchmark: " + values.CONF_BENCHMARK)
            print("\t[META-DATA] project: " + subject_name)
            print("\t[META-DATA] bug ID: " + bug_name)
            print("\t[INFO] experiment directory: " + dir_exp)

            if not os.path.isdir(tool_inst_dir):
                print("\t[INFO] instrumentation not exist for tool, skipping experiment")
                continue

            benchmark.setup(index)
            if not values.CONF_SETUP_ONLY:
                dir_result = definitions.DIR_RESULT + "/" + "-".join([config_id, benchmark.name,
                                                                                 repair_tool.name,
                                                                                 subject_name, bug_name])
                utilities.clean_results(dir_result)
                repair(dir_exp, dir_setup, experiment_item, repair_tool)
                archive_results(benchmark, repair_tool, dir_result, dir_exp)
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


def main():
    import sys
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    try:
        run(sys.argv[1:])
    except SystemExit as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
    except KeyboardInterrupt as e:
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
    except Exception as e:
        is_error = True
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, '.3f')
        time_info[definitions.KEY_DURATION_TOTAL] = str(total_duration)
        emitter.end(time_info, is_error)
        logger.end(time_info, is_error)
        logger.store()
