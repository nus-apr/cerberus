import os
import threading
import time
import traceback
from os.path import join
from typing import Any
from typing import Dict
from typing import Optional

from app.core import definitions
from app.core import emitter
from app.core import parallel
from app.core import utilities
from app.core import values
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.task.typing.TaskType import TaskType
from app.drivers.tools.slice.AbstractSliceTool import AbstractSliceTool


def run_slice(
    dir_info: DirectoryInfo,
    experiment_info,
    tool: AbstractSliceTool,
    slice_config_info: Dict[str, Any],
    container_id: Optional[str],
    benchmark_name: str,
):
    fix_location = None
    fix_source_file = ""
    fix_line_numbers = []
    experiment_info[definitions.KEY_BENCHMARK] = benchmark_name
    test_timeout = int(
        slice_config_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10)
    )

    passing_test_list = experiment_info.get(definitions.KEY_PASSING_TEST, [])
    if isinstance(passing_test_list, str):
        passing_test_list = passing_test_list.split(",")
    failing_test_list = experiment_info.get(definitions.KEY_FAILING_TEST, [])
    if isinstance(failing_test_list, str):
        failing_test_list = failing_test_list.split(",")
    if slice_config_info[definitions.KEY_CONFIG_FIX_LOC] == "file":
        fix_location = str(experiment_info.get(definitions.KEY_FIX_FILE, ""))
    elif slice_config_info[definitions.KEY_CONFIG_FIX_LOC] == "line":
        fix_source_file = str(experiment_info.get(definitions.KEY_FIX_FILE, ""))
        fix_line_numbers = list(
            map(str, experiment_info.get(definitions.KEY_FIX_LINES, []))
        )
        fix_location = "{}:{}".format(fix_source_file, ",".join(fix_line_numbers))
    elif slice_config_info[definitions.KEY_CONFIG_FIX_LOC] == "auto":
        if definitions.KEY_FIX_FILE in experiment_info:
            del experiment_info[definitions.KEY_FIX_FILE]

    experiment_info[definitions.KEY_FIX_LINES] = fix_line_numbers
    experiment_info[definitions.KEY_FIX_LOC] = fix_location

    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = test_timeout
    tool.update_info(container_id, values.only_instrument, dir_info)
    try:
        tool.run_slicing(experiment_info, slice_config_info)
        if values.experiment_status.get(TaskStatus.NONE) == TaskStatus.NONE:
            values.experiment_status.set(TaskStatus.SUCCESS)
    except Exception as ex:
        values.experiment_status.set(TaskStatus.FAIL_IN_TOOL)
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {ex}")
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {traceback.format_exc()}")


def slice_all(
    dir_info: Any,
    experiment_info: Dict[str, Any],
    slice_tool: AbstractSliceTool,
    slice_config_info,
    container_id: Optional[str],
    benchmark_name: str,
):
    consume_thread = None
    tool_thread = None
    if not values.ui_active:
        parallel.initialize()
    time_duration = float(slice_config_info.get(definitions.KEY_CONFIG_TIMEOUT, 1))
    test_timeout = int(experiment_info.get(definitions.KEY_CONFIG_TIMEOUT_TESTCASE, 10))
    total_timeout = time.time() + 60 * 60 * time_duration

    final_status = [TaskStatus.NONE]

    passing_test_list = experiment_info.get(definitions.KEY_PASSING_TEST, [])
    if isinstance(passing_test_list, str):
        passing_test_list = passing_test_list.split(",")

    failing_test_list = str(
        experiment_info.get(definitions.KEY_FAILING_TEST, "")
    ).split(",")

    if values.ui_active:
        run_slice(
            dir_info,
            experiment_info,
            slice_tool,
            slice_config_info,
            container_id,
            benchmark_name,
        )
    else:

        def slice_wrapped(
            dir_info,
            experiment_info,
            slice_tool: AbstractSliceTool,
            slice_config_info,
            container_id: Optional[str],
            benchmark_name: str,
            slice_profile_id: str,
            job_identifier: str,
            task_type: TaskType,
            final_status,
        ):
            """
            Pass over some fields as we are going into a new thread
            """
            values.task_type.set(task_type)
            values.current_task_profile_id.set(slice_profile_id)
            values.job_identifier.set(job_identifier)
            run_slice(
                dir_info,
                experiment_info,
                slice_tool,
                slice_config_info,
                container_id,
                benchmark_name,
            )
            final_status[0] = values.experiment_status.get(TaskStatus.SUCCESS)

        tool_thread = threading.Thread(
            target=slice_wrapped,
            args=(
                dir_info,
                experiment_info,
                slice_tool,
                slice_config_info,
                container_id,
                benchmark_name,
                values.current_task_profile_id.get("NA"),
                values.job_identifier.get("NA"),
                values.task_type.get(None),
                final_status,
            ),
            name="Wrapper thread for slicing {} {} {}".format(
                slice_tool.name, benchmark_name, container_id
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
                    slice_tool.name
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
                "\t\t\t[framework] {}: thread has already finished.".format(
                    slice_tool.name
                )
            )

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        tool_thread.join()
        values.experiment_status.set(final_status[0])
