import sys
import json
import subprocess
import os
import re
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
    if not os.path.isdir(definitions.DIR_EXPERIMENT):
        os.makedirs(definitions.DIR_EXPERIMENT)
    if not os.path.isdir(definitions.DIRECTORY_LOG_BASE):
        os.makedirs(definitions.DIRECTORY_LOG_BASE)


def archive_results(dir_results):
    if not os.path.isdir(dir_results):
        os.makedirs(dir_results)
    experiment_id = dir_results.split("/")[-1]
    archive_command = "cd " + dirname(abspath(dir_results)) + "; tar cvzf " + experiment_id + ".tar.gz " + experiment_id
    utilities.execute_command(archive_command)


def repair(dir_expr, dir_setup, dir_logs, experiment_info, tool: AbstractTool, config_info, container_id):
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_number = str(experiment_info[definitions.KEY_FIX_LINE])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
    binary_input_arg = experiment_info[definitions.KEY_CRASH_CMD]
    subject_name = experiment_info[definitions.KEY_SUBJECT]
    binary_path = experiment_info[definitions.KEY_BINARY_PATH]
    fix_location = None
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + fix_line_number
    experiment_info[definitions.KEY_FIX_LOC] = fix_location
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    passing_test_list = experiment_info[definitions.KEY_PASSING_TEST].split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list[:int(len(passing_test_list) * test_ratio)]
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    config_info[definitions.KEY_TOOL_PARAMS] = values.CONF_TOOL_PARAMS
    dir_info = {
        "logs": dir_logs,
        "setup": dir_setup,
        "expr": dir_expr
    }
    tool.repair(dir_info, experiment_info, config_info, container_id, values.CONF_INSTRUMENT_ONLY)


def analyse_result(dir_logs, dir_expr, dir_setup, dir_results, experiment_info, tool: AbstractTool):
    emitter.normal("\t\t[framework] analysing experiment results")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    size_space, n_enumerated, n_plausible, n_noncompile = tool.analyse_output(dir_logs, dir_results,
                                                                              dir_expr, dir_setup, bug_id,
                                                                              failing_test_list)

    conf_id = str(values.CONFIG_ID)
    exp_id = conf_id + "-" + bug_id
    values.ANALYSIS_RESULTS[exp_id] = [size_space, n_enumerated, n_plausible, n_noncompile]
    tool.print_analysis(size_space, n_enumerated, n_plausible, n_noncompile)
    logger.analysis(exp_id)


def retrieve_results(archive_name, tool: AbstractTool):
    emitter.normal("\t\tretrieving results for analysis")
    archive_path = values.DIR_MAIN + "/results/" + tool.name.lower() + "/" + archive_name
    if os.path.isfile(archive_path):
        extract_command = "cp " + archive_path + " " + definitions.DIR_RESULT + ";"
        extract_command += "cd " + definitions.DIR_RESULT + ";"
        extract_command += "tar -xf " + archive_name
        utilities.execute_command(extract_command)
        return True
    else:
        emitter.error("\t\t[error] result archive not found at " + archive_path)
        return False


def save_artifacts(dir_expr, dir_setup, dir_artifacts, experiment_info, tool: AbstractTool, container_id):
    emitter.normal("\t\t[framework] saving artifacts and cleaning up")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    tool.save_artefacts(dir_artifacts, dir_expr, dir_setup, bug_id, container_id)
    tool.post_process(dir_expr, dir_artifacts, container_id)


def show_dev_patch(dir_diff):
    regex = re.compile('(.*-diff$)')
    diff_file_path = None
    for root, dirs, files in os.walk(dir_diff):
        for file in files:
            if regex.match(file):
                diff_file_path = os.path.join(root, file)
                break
    if diff_file_path:
        with open(diff_file_path, 'r') as diff_file:
            diff_content = diff_file.readlines()
            emitter.emit_patch(diff_content)
    else:
        emitter.error("\t\t\t[error] dev-patch file not found")


def run(repair_tool, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight("[configuration] repair-tool: " + repair_tool.name)
    emitter.highlight("[configuration] repair-benchmark: " + benchmark.name)
    run_config_id_list = values.CONF_CONFIG_ID_LIST
    iteration = 0
    for config_id in run_config_id_list:
        if config_id not in setup:
            utilities.error_exit("invalid configuration id " + config_id)
        config_info = setup[config_id]
        values.CONFIG_ID = config_info[definitions.KEY_ID]
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
            if values.CONF_BUG_INDEX_LIST and str(bug_index) not in values.CONF_BUG_INDEX_LIST:
                continue
            if values.CONF_SKIP_LIST and str(bug_index) in values.CONF_SKIP_LIST:
                continue
            if values.CONF_START_INDEX and bug_index < values.CONF_START_INDEX:
                continue
            if values.CONF_END_INDEX and bug_index > values.CONF_END_INDEX:
                break
            if values.CONF_SUBJECT_NAME and values.CONF_SUBJECT_NAME != subject_name:
                continue

            subject_name = str(experiment_item[definitions.KEY_SUBJECT])

            # setup dir_paths
            directory_name = benchmark.name + "/" + subject_name + "/" + bug_name + "/"
            if values.DEFAULT_USE_CONTAINER:
                dir_setup = "/setup/" + directory_name
                dir_exp = "/experiment/" + directory_name
                dir_artifact = "/output"
            else:
                dir_setup = definitions.DIR_MAIN + "/benchmark/" + directory_name
                dir_exp = definitions.DIR_EXPERIMENT + "/" + directory_name
                dir_artifact = definitions.DIR_ARTIFACTS + "/" + directory_name
            tool_inst_dir = dir_setup + "/" + str(repair_tool.name).lower()
            dir_result = definitions.DIR_RESULT + "/" + "-".join([config_id, benchmark.name,
                                                                  repair_tool.name,
                                                                  subject_name, bug_name])

            dir_log = definitions.DIR_LOGS + "/" + "-".join([config_id, benchmark.name,
                                                             repair_tool.name,
                                                             subject_name, bug_name])

            iteration = iteration + 1
            values.ITERATION_NO = iteration
            emitter.sub_sub_title("Experiment #" + str(iteration) + " - Bug #" + str(bug_index))
            emitter.highlight("\t[configuration] identifier: " + str(config_info[definitions.KEY_ID]))
            emitter.highlight("\t[configuration] timeout: " + str(config_info[definitions.KEY_CONFIG_TIMEOUT]))
            emitter.highlight("\t[configuration] fix-loc: " + config_info[definitions.KEY_CONFIG_FIX_LOC])
            emitter.highlight("\t[configuration] test-suite ratio: " + str(config_info[definitions.KEY_CONFIG_TEST_RATIO]))
            emitter.highlight("\t[meta-data] project: " + subject_name)
            emitter.highlight("\t[meta-data] bug ID: " + bug_name)
            emitter.highlight("\t[info] experiment directory: " + dir_exp)

            if not os.path.isdir(tool_inst_dir):
                emitter.warning("\t\t[warning] there is no instrumentation for " + repair_tool.name)
                # continue

            if values.CONF_ANALYSE_ONLY:
                if not os.path.isdir(dir_result):
                    archive_name = "-".join([config_id, benchmark.name,
                                             repair_tool.name,
                                             subject_name, bug_name]) + ".tar.gz"
                    if not retrieve_results(archive_name, repair_tool):
                        continue
                analyse_result(dir_exp, dir_setup, dir_result, experiment_item, repair_tool)
                continue
            utilities.clean_results(dir_result)
            container_id = benchmark.setup(repair_tool.name, bug_index, config_id,
                                           values.DEFAULT_RUN_TESTS_ONLY,
                                           values.DEFAULT_USE_CONTAINER)
            if os.path.isdir(dir_exp):
                emitter.warning("\t\t[warning] experiment dir exists, cleaning setup")
                benchmark.clean(dir_exp, container_id)
            if not values.DEFAULT_SETUP_ONLY:
                benchmark.save_artefacts(dir_exp, dir_artifact, container_id)
                repair(dir_exp, dir_setup, dir_log, experiment_item, repair_tool, config_info, container_id)
                if not values.CONF_INSTRUMENT_ONLY:
                    save_artifacts(dir_exp, dir_setup, dir_artifact, experiment_item, repair_tool, container_id)
                    analyse_result(dir_log, dir_exp, dir_setup, dir_result, experiment_item, repair_tool)
                    archive_results(dir_result)
                if values.CONF_PURGE:
                    benchmark.clean(dir_exp, container_id)
            if values.CONF_SHOW_DEV_PATCH:
                show_dev_patch(dir_exp + "/diffs")


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
    tool.check_tool_exists()
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

