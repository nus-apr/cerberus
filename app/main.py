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
from multiprocessing import get_context, set_start_method
from app.tools import AbstractTool
from os.path import dirname, abspath
import ctypes

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
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_numbers = [str(x) for x in experiment_info[definitions.KEY_FIX_LINES]]
    experiment_info[definitions.KEY_FIX_LINES] = fix_line_numbers
    experiment_info[definitions.KEY_BENCHMARK] = benchmark_name
    fix_location = None
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + ",".join(fix_line_numbers)
    experiment_info[definitions.KEY_FIX_LOC] = fix_location
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    test_timeout = int(config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE])
    passing_id_list_str = experiment_info[definitions.KEY_PASSING_TEST]
    passing_test_list = []
    if str(passing_id_list_str).replace(",", "").isnumeric():
        passing_test_list = passing_id_list_str.split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list[:int(len(passing_test_list) * test_ratio)]
    if isinstance(failing_test_list, str):
        failing_test_list = failing_test_list.split(",")
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = test_timeout

    config_info[definitions.KEY_TOOL_PARAMS] = values.CONF_TOOL_PARAMS
    dir_output = dir_info["output"]
    dir_info_container = {
        "logs": dir_log,
        "setup": dir_setup,
        "expr": dir_expr,
        "output": dir_output
    }

    tool.repair(dir_info_container, experiment_info, config_info, container_id, values.CONF_INSTRUMENT_ONLY)


def repair_all(dir_info_list, experiment_info, tool_list, config_info, container_id_list, benchmark_name):
    consume_thread = None
    tool_thread_list = []
    parallel.initialize()
    time_duration = float(config_info[definitions.KEY_CONFIG_TIMEOUT])
    test_timeout = int(experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE])
    total_timeout = time.time() + 60 * 60 * time_duration
    for index in range(0, len(tool_list)):
        dir_info = dir_info_list[index]
        repair_tool = tool_list[index]
        container_id = container_id_list[index]
        dir_expr = dir_info["experiment"]
        dir_output = dir_info["output"]
        passing_id_list_str = experiment_info[definitions.KEY_PASSING_TEST]
        passing_test_list = []
        test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
        if str(passing_id_list_str).replace(",", "").isnumeric():
            passing_test_list = passing_id_list_str.split(",")
        failing_test_list = str(experiment_info[definitions.KEY_FAILING_TEST]).split(",")

        if index == 0:
            binary_path = experiment_info[definitions.KEY_BINARY_PATH]
            valkyrie_binary_path = dir_output + "/binary"
            binary_path = dir_expr + "/src/" + binary_path

            if container_id:
                copy_command = "docker cp {}:{} {}".format(container_id, binary_path, valkyrie_binary_path)
            else:
                copy_command = "cp {} {}".format(binary_path, valkyrie_binary_path)

            utilities.execute_command(copy_command)
            values.LIST_PROCESSED = []
            subject_name = experiment_info[definitions.KEY_SUBJECT]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            test_driver_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/test.sh".format(benchmark_name,
                                                                                           subject_name,
                                                                                           bug_id)
            test_dir_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/tests".format(benchmark_name,
                                                                                      subject_name,
                                                                                      bug_id)
            test_suite_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/test-suite".format(benchmark_name,
                                                                                             subject_name,
                                                                                             bug_id)
            oracle_path = definitions.DIR_MAIN + "/benchmark/{}/{}/{}/oracle*".format(benchmark_name,
                                                                                      subject_name,
                                                                                      bug_id)
            valkyrie_oracle_path = dir_output + "/oracle"
            if not os.path.isdir(test_suite_path):
                if os.path.isfile(valkyrie_oracle_path):
                    os.remove(valkyrie_oracle_path)
                with open(valkyrie_oracle_path, "w") as oracle_file:
                    oracle_file.writelines("#!/bin/bash\n")
                    oracle_file.writelines( "script_dir=\"$( cd \"$( dirname \"${BASH_SOURCE[0]}\" )\" &> /dev/null && pwd )\"\n")
                    oracle_file.writelines("export LD_LIBRARY_PATH=$script_dir/../../../libs\n")
                    oracle_file.writelines("$script_dir/test.sh /dev/null $@\n")
                os.system("chmod +x {}".format(valkyrie_oracle_path))
                copy_command = "cp {} {};".format(test_driver_path, dir_output)
                copy_command += "cp -rf {} {}".format(test_dir_path, dir_output)
                copy_command += "cp -rf {} {}".format(oracle_path, dir_output)
            else:
                copy_command = "cp -rf {} {}".format(test_suite_path, dir_output)
                file_list = list()
                for (dir_path, dir_names, file_names) in os.walk(test_suite_path):
                    file_list += [os.path.join(dir_path, file) for file in file_names]

                for binary_file in file_list:
                    if ".orig" in binary_file:
                        os.system("e9afl {} -o {} > /dev/null 2>&1".format(binary_file, binary_file.replace(".orig", ".inst_coverage")))
                valkyrie_oracle_path = test_suite_path + "/valkyrie-tests.sh"
                valkyrie_binary_path = None
            utilities.execute_command(copy_command)
            patch_dir = dir_output + "/patches"
            if not os.path.isdir(patch_dir):
                os.makedirs(patch_dir)
            dir_process = dir_output + "/patches-processing"
            utilities.execute_command("mkdir {}".format(dir_process))
            is_rank = len(tool_list) > 1
            validation_test_list = failing_test_list + passing_test_list[:int(len(passing_test_list) * test_ratio)]
            fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
            if values.DEFAULT_USE_VALKYRIE:
                v_path_info = (valkyrie_binary_path, valkyrie_oracle_path, fix_source_file)
                v_dir_info = (patch_dir, dir_process)
                v_config_info = (validation_test_list, is_rank, total_timeout, test_timeout)

                consume_thread = threading.Thread(target=parallel.consume_patches, args=(v_path_info,
                                                                                         v_dir_info,
                                                                                         v_config_info
                                                                                         ))
                consume_thread.start()

        if values.DEFAULT_USE_VALKYRIE:
            values.APR_TOOL_RUNNING = True
        t_thread = threading.Thread(target=repair, args=(dir_info, experiment_info,
                                                         repair_tool, config_info,
                                                         container_id, benchmark_name))
        t_thread.start()
        tool_thread_list.append((t_thread, repair_tool))

    for thread, tool in tool_thread_list:
        wait_time = 5
        if time.time() <= total_timeout:
            wait_time = total_timeout - time.time()
        thread.join(wait_time)
        if thread.is_alive():
            emitter.highlight("\t\t\t[info] {}: thread is not done, setting event to kill thread.".format(tool.name))
            event = threading.Event()
            event.set()
            # The thread can still be running at this point. For example, if the
            # thread's call to isSet() returns right before this call to set(), then
            # the thread will still perform the full 1 second sleep and the rest of
            # the loop before finally stopping.
        else:
            emitter.highlight("\t\t\t[info] {}: thread has already finished.".format(tool.name))

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        thread.join()
        if tool.log_output_path:
            timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + tool.log_output_path
            utilities.execute_command(timestamp_command)

    values.APR_TOOL_RUNNING = False
    if values.DEFAULT_USE_VALKYRIE:
        emitter.normal("\t\t\twaiting for validation pool")
        parallel.wait_validation()
        emitter.normal("\t\t\twaiting for consumer pool")
        consume_thread.join()
    for t in tool_list:
        timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + t.log_output_path
        utilities.execute_command(timestamp_command)


def analyse_result(dir_info_list, experiment_info, tool_list):
    emitter.normal("\t\t[framework] analysing experiment results")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    first_start = None
    patch_dir = None
    index = -1
    for tool in tool_list:
        index = index + 1
        dir_info = dir_info_list[index]
        space_info, time_info = tool.analyse_output(dir_info, bug_id,
                                                    failing_test_list)
        if first_start is None:
            first_start = time_info[6]
        else:
            if first_start > time_info[6]:
                first_start = time_info[6]
        conf_id = str(values.CONFIG_ID)
        exp_id = conf_id + "-" + bug_id
        values.ANALYSIS_RESULTS[exp_id] = [space_info, time_info]
        tool.print_analysis(space_info, time_info)
        tool.log_output_path = None
        logger.analysis(exp_id)
        dir_output = dir_info["output"]
        patch_dir = dir_output + "/patches"
    if values.DEFAULT_USE_VALKYRIE:
        valkyrie.analyse_output(patch_dir, first_start)


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
    dir_results = dir_info["result"]
    if not os.path.isdir(dir_results):
        os.system("mkdir -p {}".format(dir_results))
    tool.save_artefacts(dir_info, experiment_info, container_id)
    tool.post_process(dir_expr, dir_artifacts, container_id)
    save_command = "cp -f " + definitions.FILE_MAIN_LOG + " " + dir_results + ";"
    save_command += "cp -f " + definitions.FILE_ERROR_LOG + "/* " + dir_results
    utilities.execute_command(save_command)


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


def run(repair_tool_list, benchmark, setup):
    emitter.sub_title("Repairing benchmark")
    emitter.highlight("[configuration] repair-tool(s): " + " ".join([x.name for x in repair_tool_list]))
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
            config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = experiment_item[definitions.KEY_CONFIG_TIMEOUT_TESTCASE]
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

            iteration = iteration + 1
            values.ITERATION_NO = iteration
            emitter.sub_sub_title("Experiment #" + str(iteration) + " - Bug #" + str(bug_index))
            emitter.highlight("\t[configuration] identifier: " + str(config_info[definitions.KEY_ID]))
            emitter.highlight("\t[configuration] timeout: " + str(config_info[definitions.KEY_CONFIG_TIMEOUT]))
            emitter.highlight("\t[configuration] fix-loc: " + config_info[definitions.KEY_CONFIG_FIX_LOC])
            emitter.highlight(
                "\t[configuration] test-suite ratio: " + str(config_info[definitions.KEY_CONFIG_TEST_RATIO]))
            emitter.highlight("\t[meta-data] project: " + subject_name)
            emitter.highlight("\t[meta-data] bug ID: " + bug_name)
            dir_info_list = []
            container_id_list = []
            index = 0
            for repair_tool in repair_tool_list:
                index = index + 1
                tool_name = repair_tool.name
                if len(repair_tool_list) > 1:
                    tool_name = "multi"
                tool_inst_dir = definitions.DIR_MAIN + "/benchmark/" + directory_name + "/" + str(repair_tool.name).lower()
                dir_result = definitions.DIR_RESULT + "/" + "-".join([config_id, benchmark.name,
                                                                      tool_name,
                                                                      subject_name, bug_name])

                dir_log = definitions.DIR_LOGS + "/" + "-".join([config_id, benchmark.name,
                                                                 tool_name,
                                                                 subject_name, bug_name])
                dir_output = definitions.DIR_ARTIFACTS + "/" + "-".join([config_id, benchmark.name,
                                                                         tool_name,
                                                                         subject_name, bug_name])
                dir_info = {
                    "log": dir_log,
                    "output": dir_output,
                    "result": dir_result,
                    "setup": dir_setup,
                    "experiment": dir_exp,
                    "artifact": dir_artifact

                }


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
                    analyse_result([dir_info], experiment_item, [repair_tool])
                    continue
                if index == 1:
                    utilities.clean_artifacts(dir_output)
                    utilities.clean_artifacts(dir_log)
                container_id = benchmark.setup(repair_tool.name, bug_index, config_id,
                                               values.DEFAULT_RUN_TESTS_ONLY,
                                               values.DEFAULT_USE_CONTAINER, len(repair_tool_list) > 1)
                if not values.DEFAULT_SETUP_ONLY:
                    benchmark.save_artefacts(dir_exp, dir_artifact, container_id)
                container_id_list.append(container_id)
                dir_info_list.append(dir_info)
                # if os.path.isdir(dir_exp):
                #     emitter.warning("\t\t[warning] experiment dir exists, cleaning setup")
                #     benchmark.clean(dir_exp, container_id)
            if values.DEFAULT_ANALYSE_ONLY:
                continue

            if not values.DEFAULT_SETUP_ONLY:
                repair_all(dir_info_list, experiment_item, repair_tool_list, config_info, container_id_list, benchmark.name)
                if not values.CONF_INSTRUMENT_ONLY:
                    save_artifacts(dir_info, experiment_item, repair_tool, container_id)
                    analyse_result(dir_info_list, experiment_item, repair_tool_list)
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

