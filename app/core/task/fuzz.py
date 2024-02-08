import threading
import time
import traceback
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
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


def run_fuzz(
    dir_info: DirectoryInfo,
    experiment_info: Dict[str, Any],
    tool: AbstractFuzzTool,
    fuzz_config_info: Dict[str, Any],
    container_id: Optional[str],
    benchmark_name: str,
):
    experiment_info[definitions.KEY_BENCHMARK] = benchmark_name
    tool.update_info(container_id, values.only_instrument, dir_info, experiment_info)
    tool.process_tests(dir_info, experiment_info)
    try:
        tool.run_fuzz(experiment_info, fuzz_config_info)
        if values.experiment_status.get(TaskStatus.NONE) == TaskStatus.NONE:
            values.experiment_status.set(TaskStatus.SUCCESS)
    except Exception as ex:
        values.experiment_status.set(TaskStatus.FAIL_IN_TOOL)
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {ex}")
        emitter.error(f"\t\t\t[ERROR][{tool.name}]: {traceback.format_exc()}")


def fuzz_all(
    dir_info: Any,
    experiment_info: Dict[str, Any],
    fuzzer: AbstractFuzzTool,
    fuzz_config_info,
    container_id: Optional[str],
    benchmark_name: str,
):
    tool_thread = None
    if not values.ui_active:
        parallel.initialize()
    time_duration = float(fuzz_config_info.get(definitions.KEY_CONFIG_TIMEOUT, 1))
    total_timeout = time.time() + 60 * 60 * time_duration

    final_status = [TaskStatus.NONE]

    if values.ui_active:
        run_fuzz(
            dir_info,
            experiment_info,
            fuzzer,
            fuzz_config_info,
            container_id,
            benchmark_name,
        )
    else:

        def fuzz_wrapped(
            dir_info,
            experiment_info,
            fuzz_tool: AbstractFuzzTool,
            fuzz_config_info,
            container_id: Optional[str],
            benchmark_name: str,
            fuzz_profile_id: str,
            job_identifier: str,
            task_type: TaskType,
            final_status,
        ):
            """
            Pass over some fields as we are going into a new thread
            """
            values.task_type.set(task_type)
            values.current_task_profile_id.set(fuzz_profile_id)
            values.job_identifier.set(job_identifier)
            run_fuzz(
                dir_info,
                experiment_info,
                fuzz_tool,
                fuzz_config_info,
                container_id,
                benchmark_name,
            )
            final_status[0] = values.experiment_status.get(TaskStatus.SUCCESS)

        tool_thread = threading.Thread(
            target=fuzz_wrapped,
            args=(
                dir_info,
                experiment_info,
                fuzzer,
                fuzz_config_info,
                container_id,
                benchmark_name,
                values.current_task_profile_id.get("NA"),
                values.job_identifier.get("NA"),
                values.task_type.get(None),
                final_status,
            ),
            name="Wrapper thread for fuzzing {} {} {}".format(
                fuzzer.name, benchmark_name, container_id
            ),
        )
        tool_thread.start()

        if not tool_thread:
            utilities.error_exit(
                "\t\t[framework] tool thread was not created somehow??"
            )
        wait_time = 5.0
        if time.time() <= total_timeout:
            wait_time = total_timeout - time.time()
        tool_thread.join(wait_time)
        if tool_thread.is_alive():
            emitter.highlight(
                "\t\t\t[framework] thread for {} is not done, setting event to kill thread.".format(
                    fuzzer.name
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
                "\t\t\t[framework] thread for {} has already finished.".format(
                    fuzzer.name
                )
            )

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        tool_thread.join()
        values.experiment_status.set(final_status[0])
        # if tool.log_output_path:
        #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + tool.log_output_path
        #     utilities.execute_command(timestamp_command)

    values.running_tool = False
    # for t in tool_list:
    #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + t.log_output_path
    #     utilities.execute_command(timestamp_command)
