import copy
import hashlib
import os
import shutil
import threading
import time
import traceback
from os.path import dirname
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional
from typing import Tuple

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import parallel
from app.core import utilities
from app.core import values
from app.core.task.dir_info import add_instrumentation_dir_info
from app.core.task.dir_info import generate_tool_dir_info
from app.core.task.image import construct_container_volumes
from app.core.task.results import collect_tool_result
from app.core.task.results import retrieve_results
from app.core.task.results import save_artifacts
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


task_timeout_override: Dict[TaskType, str] = {
    "repair": definitions.KEY_CONFIG_REPAIR_TIMEOUT,
    "analyze": definitions.KEY_CONFIG_ANALYZE_TIMEOUT,
    "fuzz": definitions.KEY_CONFIG_FUZZ_TIMEOUT,
    "validate": definitions.KEY_CONFIG_VALIDATE_TIMEOUT,
    "localize": definitions.KEY_CONFIG_LOCALIZE_TIMEOUT,
    "select": definitions.KEY_CONFIG_SELECT_TIMEOUT,
    "composite": definitions.KEY_CONFIG_COMPOSITE_TIMEOUT,
}


def run(
    benchmark: AbstractBenchmark,
    tool: AbstractTool,
    bug_info: Dict[str, Any],
    task_config_info_template: Dict[str, Any],
    container_config_info: Dict[str, Any],
    task_identifier: str,
    cpu: List[str],
    gpu: List[str],
    run_index: str,
    task_image: Optional[str] = None,
    hash: Any = None,
    dir_setup_extended: Optional[str] = None,
    dir_logs_override: Optional[str] = None,
) -> Tuple[bool, DirectoryInfo]:
    bug_name = str(bug_info[definitions.KEY_BUG_ID])
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    task_config_info = copy.deepcopy(task_config_info_template)

    task_config_info[definitions.KEY_GPUS] = gpu
    task_config_info[definitions.KEY_CPUS] = cpu

    if definitions.KEY_CONFIG_TIMEOUT_TESTCASE in bug_info:
        task_config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = bug_info[
            definitions.KEY_CONFIG_TIMEOUT_TESTCASE
        ]

    if hash is None:
        hash = hashlib.sha1()
        hash.update(str(time.time()).encode("utf-8"))

    dir_info = generate_tool_dir_info(
        benchmark.name,
        subject_name,
        bug_name,
        hash,
        task_identifier,
        dir_setup_extended,
        dir_logs_override,
    )
    benchmark.update_dir_info(dir_info, tool.locally_running)
    print_task_info(
        task_config_info,
        container_config_info,
        bug_name,
        subject_name,
        dir_info,
        tool.locally_running,
    )

    dir_info = add_instrumentation_dir_info(dir_info, tool.name)

    dir_instr_local = dir_info["local"]["instrumentation"]
    dir_result_local = dir_info["local"]["results"]

    container_id = None
    # emitter.information("directory is {}".format(dir_instr_local))
    if os.path.isdir(dir_instr_local):
        emitter.information(
            "\t\t[framework] there is custom instrumentation for {}".format(tool.name)
        )

    if values.only_analyse:
        can_analyse_results = True
        if (
            not os.path.isdir(dir_result_local)
            or len(os.listdir(dir_result_local)) == 0
        ):
            archive_name = task_identifier + ".tar.gz"
            can_analyse_results = retrieve_results(archive_name, tool)
        if can_analyse_results:
            collect_tool_result(dir_info, bug_info, tool)
    else:
        utilities.clean_artifacts(dir_info["local"]["artifacts"])
        utilities.clean_artifacts(dir_info["local"]["logs"])
        benchmark.update_dir_info(dir_info, tool.locally_running)

        if values.use_container and not tool.locally_running:
            if tool.image_name is None:
                utilities.error_exit(
                    "Repair tool does not have a docker image name assigned: {}".format(
                        tool.name
                    )
                )

            if task_image is None:
                utilities.error_exit(
                    "No task image provided, though container mode is selected"
                )

            container_id = container.create_running_container(
                construct_container_volumes(dir_info, tool.bindings),
                task_image,
                task_identifier,
                cpu,
                gpu,
                container_config_info,
                dir_info["container"]["logs"],
                dir_info["local"]["logs"],
            )
            if not container_id:
                utilities.error_exit("Could not get container id!")

    if not values.only_setup:
        task_type = values.task_type.get()
        emitter.debug("\t\t[framework] Running task type: {}".format(task_type))
        emitter.debug(
            "\t\t[framework] Timeout override: {}".format(task_timeout_override)
        )
        emitter.debug("\t\t[framework] Task config info: {}".format(task_config_info))
        if task_type in task_timeout_override:
            task_config_info[definitions.KEY_CONFIG_TIMEOUT] = task_config_info.get(
                task_timeout_override[task_type],
                task_config_info[definitions.KEY_CONFIG_TIMEOUT],
            )

        execute(
            dir_info,
            bug_info,
            tool,
            task_config_info,
            container_config_info,
            container_id,
            benchmark,
            run_index,
            hash,
        )

        # update container stats
        if values.use_container and not tool.locally_running:
            if not container_id:
                utilities.error_exit("Use container but ID is none?")
            tool.update_container_stats(container_id)

        if not values.only_instrument:
            collect_tool_result(dir_info, bug_info, tool)
            save_artifacts(dir_info, tool)
            dir_archive = join(values.dir_results, tool.name)
            dir_result = dir_info["local"]["results"]
            utilities.archive_results(dir_result, dir_archive)
            if values.compact_results:
                utilities.clean_artifacts(dir_result)

        final_status = values.experiment_status.get(TaskStatus.NONE)
        if final_status != TaskStatus.SUCCESS and final_status != TaskStatus.TIMEOUT:
            emitter.error(
                "\t\t\t[framework] Experiment failed with status {}".format(
                    final_status
                )
            )

    return (tool.stats.error_stats.is_error, dir_info)


def setup_localization(
    experiment_info: Dict[str, Any],
    config_info: Dict[str, Any],
) -> None:
    # TODO: make better
    if (
        definitions.KEY_ANALYSIS_OUTPUT in experiment_info
        and definitions.KEY_LOCALIZATION
        in experiment_info[definitions.KEY_ANALYSIS_OUTPUT][-1]
    ):
        experiment_info[definitions.KEY_LOCALIZATION] = experiment_info[
            definitions.KEY_ANALYSIS_OUTPUT
        ][-1][definitions.KEY_LOCALIZATION]

    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "tool":
        if definitions.KEY_LOCALIZATION in experiment_info:
            del experiment_info[definitions.KEY_LOCALIZATION]
    elif config_info[definitions.KEY_CONFIG_FIX_LOC] == "file":
        if definitions.KEY_LOCALIZATION in experiment_info:
            for localization in experiment_info[definitions.KEY_LOCALIZATION]:
                del localization[definitions.KEY_FIX_LINES]


def setup_tests(
    experiment_info: Dict[str, Any],
    config_info: Dict[str, Any],
) -> None:
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    test_timeout = int(config_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10))
    passing_test_identifiers_list = experiment_info.get(
        definitions.KEY_PASSING_TEST, []
    )
    if isinstance(passing_test_identifiers_list, str):
        passing_test_identifiers_list = passing_test_identifiers_list.split(",")
    failing_test_identifiers_list = experiment_info.get(
        definitions.KEY_FAILING_TEST, []
    )
    if isinstance(failing_test_identifiers_list, str):
        failing_test_identifiers_list = failing_test_identifiers_list.split(",")
    pass_test_count = int(len(passing_test_identifiers_list) * test_ratio)
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_identifiers_list[
        :pass_test_count
    ]
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_identifiers_list
    experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = test_timeout


def execute_setup(
    dir_info: DirectoryInfo,
    experiment_info: Dict[str, Any],
    tool: AbstractTool,
    config_info: Dict[str, Any],
    container_config_info: Dict[str, Any],
    container_id: Optional[str],
    benchmark: AbstractBenchmark,
    run_index: str,
    hash: Any,
) -> None:
    experiment_info[definitions.KEY_BENCHMARK] = benchmark.name

    setup_localization(experiment_info, config_info)
    setup_tests(experiment_info, config_info)

    tool.update_info(container_id, values.only_instrument, dir_info, experiment_info)
    tool.process_tests(dir_info, config_info, experiment_info)
    try:
        tool.invoke_advanced(
            dir_info,
            benchmark,
            experiment_info,
            config_info,
            container_config_info,
            run_index,
            hash,
        )
        if values.experiment_status.get(TaskStatus.NONE) == TaskStatus.NONE:
            values.experiment_status.set(TaskStatus.SUCCESS)
    except Exception as ex:
        values.experiment_status.set(TaskStatus.FAIL_IN_TOOL)
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {ex}")
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {traceback.format_exc()}")
    pass


def setup_for_valkyrie(
    dir_info: DirectoryInfo,
    container_id: Optional[str],
    bug_info: Dict[str, Any],
    benchmark_name: str,
) -> Tuple[str, str, Optional[str], str]:
    dir_output_local = dir_info["local"]["artifacts"]
    if container_id:
        dir_expr = dir_info["container"]["experiment"]
    else:
        dir_expr = dir_info["local"]["experiment"]
    binary_path_rel = bug_info.get(definitions.KEY_BINARY_PATH, "")
    valkyrie_binary_path: Optional[str]
    valkyrie_binary_path = os.path.join(dir_output_local, "binary")
    binary_path = os.path.join(dir_expr, "src", binary_path_rel)
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
        for dir_path, _, file_names in os.walk(test_suite_path):
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
    os.makedirs(dir_process, exist_ok=True)
    return patch_dir, dir_process, valkyrie_binary_path, valkyrie_oracle_path


def execute(
    dir_info: DirectoryInfo,
    experiment_info: Dict[str, Any],
    tool: AbstractTool,
    task_config_info: Dict[str, Any],
    container_config_info: Dict[str, Any],
    container_id: Optional[str],
    benchmark: AbstractBenchmark,
    run_index: str,
    hash: Any,
) -> None:
    consume_thread = None
    tool_thread = None
    if not values.ui_active:
        parallel.initialize()

    time_duration = float(task_config_info.get(definitions.KEY_CONFIG_TIMEOUT, 1))
    test_timeout = int(experiment_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10))
    total_timeout = time.time() + 60 * 60 * time_duration

    final_status = [TaskStatus.NONE]

    passing_test_identifiers_list = experiment_info.get(
        definitions.KEY_PASSING_TEST, []
    )
    if isinstance(passing_test_identifiers_list, str):
        passing_test_identifiers_list = passing_test_identifiers_list.split(",")

    test_ratio = float(task_config_info[definitions.KEY_CONFIG_TEST_RATIO])
    failing_test_identifiers_list = str(
        experiment_info.get(definitions.KEY_FAILING_TEST, "")
    ).split(",")

    is_rank = False
    validation_test_list = (
        failing_test_identifiers_list
        + passing_test_identifiers_list[
            : int(len(passing_test_identifiers_list) * test_ratio)
        ]
    )

    if values.use_valkyrie:
        fix_source_file = str(
            experiment_info.get(definitions.KEY_LOCALIZATION, [{}])[0].get(
                definitions.KEY_FIX_FILE, ""
            )
        )
        valkyrie_setup_info = setup_for_valkyrie(
            dir_info, container_id, experiment_info, benchmark.name
        )
        patch_dir, dir_process, binary_path, oracle_path = valkyrie_setup_info
        v_path_info = (binary_path, oracle_path, fix_source_file)
        v_dir_info = (patch_dir, dir_process)
        v_task_config_info = (
            validation_test_list,
            is_rank,
            total_timeout,
            test_timeout,
        )

        def consume_patches_wrapped(
            v_path_info: Tuple[str, str, str],
            v_dir_info: Tuple[str, str],
            v_task_config_info: Dict[str, Any],
            task_profile_id: str,
            job_identifier: str,
            session_identifier: str,
            task_type: TaskType,
        ) -> None:
            """
            Pass over some fields as we are going into a new thread
            """
            values.task_type.set(task_type)
            values.current_task_profile_id.set(task_profile_id)
            values.job_identifier.set(job_identifier)
            values.session_identifier.set(session_identifier)
            parallel.consume_patches(v_path_info, v_dir_info, v_task_config_info)

        consume_thread = threading.Thread(
            target=consume_patches_wrapped,
            args=(
                v_path_info,
                v_dir_info,
                v_task_config_info,
                values.current_task_profile_id.get("NA"),
                values.job_identifier.get("NA"),
                values.session_identifier.get("NA"),
                values.task_type.get("NA"),
            ),
        )
        consume_thread.start()
        values.running_tool = True

    if values.ui_active:
        execute_setup(
            dir_info,
            experiment_info,
            tool,
            task_config_info,
            container_config_info,
            container_id,
            benchmark,
            run_index,
            hash,
        )
    else:

        def execute_wrapped(
            dir_info: DirectoryInfo,
            experiment_info: Dict[str, Any],
            tool: AbstractTool,
            task_config_info: Dict[str, Any],
            container_config_info: Dict[str, Any],
            container_id: Optional[str],
            benchmark: AbstractBenchmark,
            run_index: str,
            task_profile_id: str,
            job_identifier: str,
            session_identifier: str,
            task_type: TaskType,
            final_status: List[TaskStatus],
            hash: Any,
        ) -> None:
            """
            Pass over contextvars fields as we are going into a new thread
            """
            values.task_type.set(task_type)
            values.current_task_profile_id.set(task_profile_id)
            values.job_identifier.set(job_identifier)
            values.session_identifier.set(session_identifier)
            execute_setup(
                dir_info,
                experiment_info,
                tool,
                task_config_info,
                container_config_info,
                container_id,
                benchmark,
                run_index,
                hash,
            )
            final_status[0] = values.experiment_status.get(TaskStatus.SUCCESS)

        tool_thread = threading.Thread(
            target=execute_wrapped,
            args=(
                dir_info,
                experiment_info,
                tool,
                task_config_info,
                container_config_info,
                container_id,
                benchmark,
                run_index,
                values.current_task_profile_id.get("NA"),
                values.job_identifier.get("NA"),
                values.session_identifier.get("NA"),
                values.task_type.get(None),
                final_status,
                hash,
            ),
            name="Wrapper thread for {} {} {} {} {}".format(
                values.task_type.get("N/A"),
                tool.name,
                tool.tool_tag,
                benchmark.name,
                container_id,
            ),
        )
        tool_thread.start()

        if tool_thread is None:
            utilities.error_exit("Thread was not created")
        wait_time = 5.0
        if time.time() <= total_timeout:
            wait_time = total_timeout - time.time()
        # give 5 min grace period for threads to finish
        wait_time = wait_time + 60.0 * 5
        tool_thread.join(wait_time)

        if tool_thread.is_alive():
            emitter.highlight(
                "\t\t\t[framework] {}: thread is not done, setting event to kill thread.".format(
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
                "\t\t\t[framework] {}: thread has already finished.".format(tool.name)
            )

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        tool_thread.join()
        values.experiment_status.set(final_status[0])
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


def print_task_info(
    task_config_info: Dict[str, Any],
    container_config_info: Dict[str, Any],
    bug_name: str,
    subject_name: str,
    dir_info: DirectoryInfo,
    locally_running: bool,
) -> None:
    emitter.highlight(
        "\t\t[task profile] Identifier: {}".format(task_config_info[definitions.KEY_ID])
    )
    emitter.highlight(
        "\t\t[task profile] Timeout: {}".format(
            task_config_info[definitions.KEY_CONFIG_TIMEOUT]
        )
    )
    emitter.highlight(
        "\t\t[task profile] Fix-Loc: {}".format(
            task_config_info[definitions.KEY_CONFIG_FIX_LOC]
        )
    )
    emitter.highlight(
        "\t\t[task profile] Patch-Dir: {}".format(
            task_config_info.get(definitions.KEY_CONFIG_PATCH_DIR, None)
        )
    )
    emitter.highlight(
        "\t\t[task profile] Test-suite ratio: {}".format(
            task_config_info[definitions.KEY_CONFIG_TEST_RATIO]
        )
    )

    if values.use_container and not locally_running:
        emitter.highlight(
            "\t\t[container profile] Identifier: {}".format(
                container_config_info[definitions.KEY_ID]
            )
        )

        emitter.highlight(
            "\t\t[container profile] CPU Count: {}".format(
                container_config_info[definitions.KEY_CONTAINER_CPU_COUNT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] GPU Count: {}".format(
                container_config_info[definitions.KEY_CONTAINER_GPU_COUNT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] RAM Limit: {}".format(
                container_config_info[definitions.KEY_CONTAINER_MEM_LIMIT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] Enable Network: {}".format(
                container_config_info[definitions.KEY_CONTAINER_ENABLE_NETWORK]
            )
        )

    emitter.highlight("\t\t[meta-data] Project: {}".format(subject_name))
    emitter.highlight("\t\t[meta-data] Bug ID: {}".format(bug_name))
    emitter.highlight(
        "\t\t[meta-data] Logs directory: {}".format(dir_info["local"]["logs"])
    )
    emitter.highlight(
        "\t\t[meta-data] Output directory: {}".format(dir_info["local"]["artifacts"])
    )
    emitter.highlight(
        "\t\t[meta-data] Summary directory: {}".format(values.dir_summaries)
    )
