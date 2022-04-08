import sys
import json
import subprocess
import threading
import os
import re
import traceback
import signal
import time
from app import emitter, logger, definitions, values, utilities, configuration, parallel, valkyrie
from app.benchmarks import AbstractBenchmark
from app.tools import AbstractTool
from os.path import dirname, abspath

start_time = 0
end_time = 0


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


def archive_results(dir_results, dir_archive):
    if not os.path.isdir(dir_results):
        os.makedirs(dir_results)
    experiment_id = dir_results.split("/")[-1]
    if not os.path.isdir(dir_archive):
        os.makedirs(dir_archive)
    archive_command = "cd " + dirname(abspath(dir_results)) + "; tar cvzf " + experiment_id + ".tar.gz " + experiment_id
    archive_command += "; mv {} {}".format(experiment_id + ".tar.gz", dir_archive)
    utilities.execute_command(archive_command)


def repair(dir_info, experiment_info, tool: AbstractTool, config_info, container_id, benchmark_name):
    dir_expr = dir_info["experiment"]
    dir_setup = dir_info["setup"]
    dir_log = dir_info["log"]
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_numbers = [str(x) for x in experiment_info[definitions.KEY_FIX_LINES]]
    experiment_info[definitions.KEY_FIX_LINES] = fix_line_numbers
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
    binary_input_arg = experiment_info[definitions.KEY_CRASH_CMD]
    subject_name = experiment_info[definitions.KEY_SUBJECT]
    binary_path = experiment_info[definitions.KEY_BINARY_PATH]
    fix_location = None
    consume_limit = definitions.APR_MIN_LIMIT[tool.name]
    max_limit = definitions.APR_MAX_LIMIT[tool.name]
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + ",".join(fix_line_numbers)
    experiment_info[definitions.KEY_FIX_LOC] = fix_location
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    passing_id_list_str = experiment_info[definitions.KEY_PASSING_TEST]
    passing_test_list = []
    if str(passing_id_list_str).replace(",", "").isnumeric():
        passing_test_list = passing_id_list_str.split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST].split(",")
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list[:int(len(passing_test_list) * test_ratio)]
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    validation_test_list = failing_test_list + passing_test_list[:int(len(passing_test_list) * test_ratio)]
    config_info[definitions.KEY_TOOL_PARAMS] = values.CONF_TOOL_PARAMS
    dir_output = dir_info["output"]
    dir_info_container = {
        "logs": dir_log,
        "setup": dir_setup,
        "expr": dir_expr,
        "output": dir_output
    }
    valkyrie_binary_path = dir_output + "/binary"
    binary_path = dir_expr + "/src/" + binary_path
    libasan2_path_container = "/usr/lib/x86_64-linux-gnu/libasan.so.2.0.0"
    libasan2_path_local = dir_output + "/libasan.so.2"
    if container_id:
        copy_command = "docker cp {}:{} {};".format(container_id, binary_path, valkyrie_binary_path)
        copy_command += "docker cp {}:{} {}".format(container_id, libasan2_path_container, libasan2_path_local)
    else:
        copy_command = "cp {} {}".format(binary_path, valkyrie_binary_path)
    utilities.execute_command(copy_command)
    values.LIST_PROCESSED = []
    test_driver_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/test.sh".format(benchmark_name, subject_name, bug_id)
    test_dir_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/tests".format(benchmark_name, subject_name, bug_id)
    oracle_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/oracle*".format(benchmark_name, subject_name, bug_id)
    valkyrie_oracle_path = dir_output + "/oracle"
    if os.path.isfile(valkyrie_oracle_path):
        os.remove(valkyrie_oracle_path)
    with open(valkyrie_oracle_path, "w") as oracle_file:
        oracle_file.writelines("#!/bin/bash\n")
        oracle_file.writelines("script_dir=\"$( cd \"$( dirname \"${BASH_SOURCE[0]}\" )\" &> /dev/null && pwd )\"\n")
        oracle_file.writelines("$script_dir/test.sh /dev/null $@")
    os.system("chmod +x {}".format(valkyrie_oracle_path))
    copy_command = "cp {} {};".format(test_driver_path, dir_output)
    copy_command += "cp -rf {} {}".format(test_dir_path, dir_output)
    copy_command += "cp -rf {} {}".format(oracle_path, dir_output)
    utilities.execute_command(copy_command)
    patch_dir = dir_output + "/patches"
    if not os.path.isdir(patch_dir):
        os.makedirs(patch_dir)
    dir_process = dir_output + "/patches-processing"
    utilities.execute_command("mkdir {}".format(dir_process))
    if values.DEFAULT_USE_VALKYRIE:
        values.APR_TOOL_RUNNING = True
        t1 = threading.Thread(target=parallel.consume_patches, args=(valkyrie_binary_path, valkyrie_oracle_path,
                                                                     validation_test_list,
                                                                     fix_source_file, patch_dir, dir_process))
        t1.start()
    tool.repair(dir_info_container, experiment_info, config_info, container_id, values.CONF_INSTRUMENT_ONLY)
    values.APR_TOOL_RUNNING = False
    if values.DEFAULT_USE_VALKYRIE:
        parallel.wait_validation()
        t1.join()
        timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') >> " + tool.log_output_path
        utilities.execute_command(timestamp_command)


def analyse_result(dir_info, experiment_info, tool: AbstractTool):
    emitter.normal("\t\t[framework] analysing experiment results")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    space_info, time_info = tool.analyse_output(dir_info, bug_id,
                                                failing_test_list)
    conf_id = str(values.CONFIG_ID)
    exp_id = conf_id + "-" + bug_id
    values.ANALYSIS_RESULTS[exp_id] = [space_info, time_info]
    tool.print_analysis(space_info, time_info)
    tool.log_output_path = None
    logger.analysis(exp_id)
    dir_output = dir_info["output"]
    patch_dir = dir_output + "/patches"
    if values.DEFAULT_USE_VALKYRIE:
        valkyrie.analyse_output(patch_dir)


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


def save_artifacts(dir_info, experiment_info, tool: AbstractTool, container_id):
    emitter.normal("\t\t[framework] saving artifacts and cleaning up")
    dir_expr = dir_info["experiment"]
    dir_artifacts = dir_info["artifact"]
    tool.save_artefacts(dir_info, experiment_info, container_id)
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
            dir_output = definitions.DIR_ARTIFACTS + "/" + "-".join([config_id, benchmark.name,
                                                             repair_tool.name,
                                                             subject_name, bug_name])
            dir_info = {
                "log": dir_log,
                "output": dir_output,
                "result": dir_result,
                "setup": dir_setup,
                "experiment": dir_exp,
                "artifact": dir_artifact

            }
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

            if values.DEFAULT_ANALYSE_ONLY:
                if not os.path.isdir(dir_result) or len(os.listdir(dir_result)) == 0:
                    archive_name = "-".join([config_id, benchmark.name,
                                             repair_tool.name,
                                             subject_name, bug_name]) + ".tar.gz"
                    if not retrieve_results(archive_name, repair_tool):
                        continue
                analyse_result(dir_info, experiment_item, repair_tool)
                continue
            utilities.clean_artifacts(dir_output)
            utilities.clean_artifacts(dir_log)
            container_id = benchmark.setup(repair_tool.name, bug_index, config_id,
                                           values.DEFAULT_RUN_TESTS_ONLY,
                                           values.DEFAULT_USE_CONTAINER)
            # if os.path.isdir(dir_exp):
            #     emitter.warning("\t\t[warning] experiment dir exists, cleaning setup")
            #     benchmark.clean(dir_exp, container_id)
            if not values.DEFAULT_SETUP_ONLY:
                benchmark.save_artefacts(dir_exp, dir_artifact, container_id)
                repair(dir_info, experiment_item, repair_tool, config_info, container_id, benchmark.name)
                if not values.CONF_INSTRUMENT_ONLY:
                    save_artifacts(dir_info, experiment_item, repair_tool, container_id)
                    analyse_result(dir_info, experiment_item, repair_tool)
                    dir_archive = definitions.DIR_RESULT + "/" + repair_tool.name
                    archive_results(dir_result, dir_archive)
                    utilities.clean_artifacts(dir_result)
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

