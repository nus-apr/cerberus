import hashlib
import os
import threading
import time
from os.path import abspath
from os.path import dirname
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import parallel
from app.core import ui
from app.core import utilities
from app.core import values
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool
from app.plugins import valkyrie


def run_repair(
    dir_info: Dict[str, Dict[str, str]],
    experiment_info,
    tool: AbstractRepairTool,
    config_info: Dict[str, Any],
    container_id: Optional[str],
    benchmark_name: str,
):
    fix_source_file = str(experiment_info.get(definitions.KEY_FIX_FILE, ""))
    fix_line_numbers = [
        str(x) for x in experiment_info.get(definitions.KEY_FIX_LINES, [])
    ]
    experiment_info[definitions.KEY_FIX_LINES] = fix_line_numbers
    experiment_info[definitions.KEY_BENCHMARK] = benchmark_name
    fix_location = None
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = "{}:{}".format(fix_source_file, ",".join(fix_line_numbers))
    experiment_info[definitions.KEY_FIX_LOC] = fix_location
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    test_timeout = int(config_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10))
    passing_id_list_str = experiment_info.get(definitions.KEY_PASSING_TEST, "")
    passing_test_list = []
    if str(passing_id_list_str).replace(",", "").isnumeric():
        passing_test_list = passing_id_list_str.split(",")
    failing_test_list = experiment_info.get(definitions.KEY_FAILING_TEST, [])
    if isinstance(failing_test_list, str):
        failing_test_list = failing_test_list.split(",")
    pass_test_count = int(len(passing_test_list) * test_ratio)
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list[:pass_test_count]
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = test_timeout
    config_info[definitions.KEY_TOOL_PARAMS] = values.tool_params
    tool.update_info(container_id, values.only_instrument, dir_info)
    tool.run_repair(experiment_info, config_info)


def setup_for_valkyrie(dir_info, container_id: Optional[str], bug_info, benchmark_name):
    dir_output_local = dir_info["local"]["artifacts"]
    if container_id:
        dir_expr = dir_info["container"]["experiment"]
    else:
        dir_expr = dir_info["local"]["experiment"]
    binary_path_rel = bug_info.get(definitions.KEY_BINARY_PATH, "")
    valkyrie_binary_path: Optional[str]
    valkyrie_binary_path = join(dir_output_local, "binary")
    binary_path = join(dir_expr, "src", binary_path_rel)
    if container_id:
        copy_command = "docker -H {} cp {}:{} {}".format(
            values.docker_host, container_id, binary_path, valkyrie_binary_path
        )
    else:
        copy_command = "cp {} {} ;".format(binary_path, valkyrie_binary_path)

    utilities.execute_command(copy_command)
    values.list_processed = []
    subject_name = bug_info[definitions.KEY_SUBJECT]
    bug_id = str(bug_info[definitions.KEY_BUG_ID])

    test_driver_path = values.dir_main + "/benchmark/{}/{}/{}/test.sh".format(
        benchmark_name, subject_name, bug_id
    )
    test_dir_path = values.dir_main + "/benchmark/{}/{}/{}/tests".format(
        benchmark_name, subject_name, bug_id
    )
    test_suite_path = values.dir_main + "/benchmark/{}/{}/{}/test-suite".format(
        benchmark_name, subject_name, bug_id
    )
    oracle_path = values.dir_main + "/benchmark/{}/{}/{}/oracle*".format(
        benchmark_name, subject_name, bug_id
    )
    valkyrie_oracle_path = dir_output_local + "/oracle"
    if not os.path.isdir(test_suite_path):
        if os.path.isfile(valkyrie_oracle_path):
            os.remove(valkyrie_oracle_path)
        with open(valkyrie_oracle_path, "w") as oracle_file:
            oracle_file.writelines("#!/bin/bash\n")
            oracle_file.writelines(
                'script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"\n'
            )
            oracle_file.writelines("export LD_LIBRARY_PATH=$script_dir/../../../libs\n")
            oracle_file.writelines("$script_dir/test.sh /dev/null $@\n")
        os.system("chmod +x {}".format(valkyrie_oracle_path))
        copy_command = "cp {} {} ; ".format(test_driver_path, dir_output_local)
        copy_command += "cp -rf {} {} ; ".format(test_dir_path, dir_output_local)
        copy_command += "cp -rf {} {}".format(oracle_path, dir_output_local)
    else:
        copy_command = "cp -rf {} {}".format(test_suite_path, dir_output_local)
        file_list = list()
        for (dir_path, _, file_names) in os.walk(test_suite_path):
            file_list += [os.path.join(dir_path, file) for file in file_names]

        for binary_file in file_list:
            if ".orig" in binary_file:
                os.system(
                    "e9afl {} -o {} > /dev/null 2>&1".format(
                        binary_file, binary_file.replace(".orig", ".inst_coverage")
                    )
                )
        valkyrie_oracle_path = test_suite_path + "/valkyrie-tests.sh"
        valkyrie_binary_path = None
    utilities.execute_command(copy_command)
    patch_dir = dir_output_local + "/patches"
    if not os.path.isdir(patch_dir):
        os.makedirs(patch_dir)
    dir_process = dir_output_local + "/patches-processing"
    utilities.execute_command("mkdir {}".format(dir_process))
    return patch_dir, dir_process, valkyrie_binary_path, valkyrie_oracle_path


def repair_all(
    dir_info_list: List[Any],
    experiment_info: Dict[str, Any],
    tool_list: List[AbstractRepairTool],
    config_info,
    container_id_list: List[str],
    benchmark_name: str,
):
    consume_thread = None
    tool_thread_list = []
    if not values.ui_active:
        parallel.initialize()
    time_duration = float(config_info.get(definitions.KEY_CONFIG_TIMEOUT, 1))
    test_timeout = int(experiment_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10))
    total_timeout = time.time() + 60 * 60 * time_duration

    for index, (dir_info, repair_tool, container_id) in enumerate(
        zip(dir_info_list, tool_list, container_id_list)
    ):
        passing_id_list_str = experiment_info.get(definitions.KEY_PASSING_TEST, "")
        passing_test_list = []
        test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
        if str(passing_id_list_str).replace(",", "").isnumeric():
            passing_test_list = passing_id_list_str.split(",")
        failing_test_list = str(
            experiment_info.get(definitions.KEY_FAILING_TEST, "")
        ).split(",")

        if index == 0:
            is_rank = len(tool_list) > 1
            validation_test_list = (
                failing_test_list
                + passing_test_list[: int(len(passing_test_list) * test_ratio)]
            )
            fix_source_file = str(experiment_info.get(definitions.KEY_FIX_FILE, ""))

            if values.use_valkyrie:
                valkyrie_setup_info = setup_for_valkyrie(
                    dir_info, container_id, experiment_info, benchmark_name
                )
                patch_dir, dir_process, binary_path, oracle_path = valkyrie_setup_info
                v_path_info = (binary_path, oracle_path, fix_source_file)
                v_dir_info = (patch_dir, dir_process)
                v_config_info = (
                    validation_test_list,
                    is_rank,
                    total_timeout,
                    test_timeout,
                )

                def consume_patches_wrapped(
                    v_path_info, v_dir_info, v_config_info, profile_id
                ):
                    values.current_profile_id.set(profile_id)
                    parallel.consume_patches(v_path_info, v_dir_info, v_config_info)

                consume_thread = threading.Thread(
                    target=consume_patches_wrapped,
                    args=(
                        v_path_info,
                        v_dir_info,
                        v_config_info,
                        values.current_profile_id.get("NA"),
                    ),
                )
                consume_thread.start()

        if values.use_valkyrie:
            values.running_tool = True

        if values.ui_active:
            run_repair(
                dir_info,
                experiment_info,
                repair_tool,
                config_info,
                container_id,
                benchmark_name,
            )
        else:

            def repair_wrapped(
                dir_info,
                experiment_info,
                repair_tool,
                config_info,
                container_id,
                benchmark_name,
                profile_id,
            ):
                values.current_profile_id.set(profile_id)
                run_repair(
                    dir_info,
                    experiment_info,
                    repair_tool,
                    config_info,
                    container_id,
                    benchmark_name,
                )

            t_thread = threading.Thread(
                target=repair_wrapped,
                args=(
                    dir_info,
                    experiment_info,
                    repair_tool,
                    config_info,
                    container_id,
                    benchmark_name,
                    values.current_profile_id.get("NA"),
                ),
            )
            t_thread.start()
            tool_thread_list.append((t_thread, repair_tool))

    if not values.ui_active:
        for thread, tool in tool_thread_list:
            wait_time = 5.0
            if time.time() <= total_timeout:
                wait_time = total_timeout - time.time()
            thread.join(wait_time)
            if thread.is_alive():
                emitter.highlight(
                    "\t\t\t[info] {}: thread is not done, setting event to kill thread.".format(
                        tool.name
                    )
                )
                event = threading.Event()
                event.set()
                # The thread can still be running at this point. For example, if the
                # thread's call to isSet() returns right before this call to set(), then
                # the thread will still perform the full 1 second sleep and the rest of
                # the loop before finally stopping.
            else:
                emitter.highlight(
                    "\t\t\t[info] {}: thread has already finished.".format(tool.name)
                )

            # Thread can still be alive at this point. Do another join without a timeout
            # to verify thread shutdown.
            thread.join()
            # if tool.log_output_path:
            #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + tool.log_output_path
            #     utilities.execute_command(timestamp_command)

        values.running_tool = False
        if values.use_valkyrie:
            emitter.normal("\t\t\twaiting for validation pool")
            parallel.wait_validation()
            emitter.normal("\t\t\twaiting for consumer pool")
            if consume_thread:
                consume_thread.join()
    # for t in tool_list:
    #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + t.log_output_path
    #     utilities.execute_command(timestamp_command)
