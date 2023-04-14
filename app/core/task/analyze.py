import threading
import time
from typing import Any
from typing import Dict
from typing import Optional

from app.core import definitions
from app.core import emitter
from app.core import parallel
from app.core import utilities
from app.core import values
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


def run_analysis(
    dir_info: Dict[str, Dict[str, str]],
    experiment_info,
    tool: AbstractAnalyzeTool,
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
    tool.run_analysis(experiment_info, config_info)


def analyze_all(
    dir_info: Any,
    experiment_info: Dict[str, Any],
    analyze_tool: AbstractAnalyzeTool,
    config_info,
    container_id: Optional[str],
    benchmark_name: str,
):
    consume_thread = None
    tool_thread = None
    if not values.ui_active:
        parallel.initialize()
    time_duration = float(config_info.get(definitions.KEY_CONFIG_TIMEOUT, 1))
    total_timeout = time.time() + 60 * 60 * time_duration

    if values.use_valkyrie:
        values.running_tool = True

    if values.ui_active:
        run_analysis(
            dir_info,
            experiment_info,
            analyze_tool,
            config_info,
            container_id,
            benchmark_name,
        )
    else:

        def analyze_wrapped(
            dir_info,
            experiment_info,
            repair_tool,
            config_info,
            container_id,
            benchmark_name,
            profile_id,
            job_identifier,
        ):
            """
            Pass over some fields as we are going into a new thread
            """
            values.current_profile_id.set(profile_id)
            values.job_identifier.set(job_identifier)
            run_analysis(
                dir_info,
                experiment_info,
                repair_tool,
                config_info,
                container_id,
                benchmark_name,
            )

        tool_thread = threading.Thread(
            target=analyze_wrapped,
            args=(
                dir_info,
                experiment_info,
                analyze_tool,
                config_info,
                container_id,
                benchmark_name,
                values.current_profile_id.get("NA"),
                values.job_identifier.get("NA"),
            ),
        )
        tool_thread.start()

    if not values.ui_active:
        if not tool_thread:
            utilities.error_exit("Tool thread was not created somehow??")
        wait_time = 5.0
        if time.time() <= total_timeout:
            wait_time = total_timeout - time.time()
        tool_thread.join(wait_time)
        if tool_thread.is_alive():
            emitter.highlight(
                "\t\t\t[info] {}: thread is not done, setting event to kill thread.".format(
                    analyze_tool.name
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
                "\t\t\t[info] {}: thread has already finished.".format(
                    analyze_tool.name
                )
            )

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        tool_thread.join()
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
