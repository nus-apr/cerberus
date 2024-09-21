import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.SliceToolStats import SliceToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.slice.AbstractSliceTool import AbstractSliceTool


class AutoBug(AbstractSliceTool):
    #TODO recheck
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/autobug"
        self.id = ""
        self.report_path = ""

    def rerun_configuration(self, config_script: str, build_script: str) -> None:
        self.emit_normal("re-running configuration and build")
        _config_path = self.dir_expr + f"/{self.name}-config-build"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f"{config_script} {self.dir_expr}\n",
                f"{build_script} {self.dir_expr}\n",
            ],
            _config_path,
        )
        reconfig_command = "bash {}".format(_config_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-re-config-build.log")
        self.run_command(reconfig_command, log_file_path=log_reconfig_path)

    def instrument(self, bug_info: Dict[str, Any]) -> None:
        benchmark_name = bug_info[self.key_benchmark]
        binary_path = bug_info.get(self.key_bin_path, None)
        if not binary_path:
            self.error_exit(f"{self.name} requires a binary path as input")
        config_script = bug_info.get(self.key_config_script, None)
        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        build_script = bug_info.get(self.key_build_script, None)
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")
        config_script = str(join(self.dir_setup, config_script))
        build_script = str(join(self.dir_setup, build_script))
        self.clean_subject(bug_info)
        self.rerun_configuration(config_script, build_script)
        sbfl_dir = "/opt/autobug/sbfl"
        abs_binary_path = str(join(self.dir_expr, "src", binary_path))
        instrument_command = f"./sbfl-tool instrument {abs_binary_path}"
        log_instrument_path = join(self.dir_logs, f"{self.name}-instrument.log")
        self.run_command(
            instrument_command, log_file_path=log_instrument_path, dir_path=sbfl_dir
        )
        instrumented_binary = abs_binary_path.split("/")[-1] + ".sbfl"
        move_command = f"mv {instrumented_binary} {abs_binary_path}"
        self.run_command(move_command, dir_path=sbfl_dir)

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        test_script = bug_info.get(self.key_test_script, None)

        if not test_script:
            self.error_exit(f"{self.name} requires a test script as input")

        test_script_path = join(self.dir_setup, test_script)
        src_dir = join(self.dir_expr, "src")
        self.report_path = str(join(self.dir_output, "report.txt"))

        if not bug_info[self.key_failing_test_identifiers]:
            self.error_exit("This tool requires negative test cases")

        failing_test_ids = bug_info[self.key_failing_test_identifiers]
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]
        self.timestamp_log_start()
        for _t in failing_test_ids:
            trace_command = f"{test_script_path} {_t}"
            self.run_command(trace_command, dir_path=self.dir_output)

        slice_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h ./autobug {1} {2}".format(
                timeout, src_dir, join(self.dir_output, "SBFL.trace")
            )
            + additional_tool_param
            + "'"
        )

        status = self.run_command(
            slice_command, self.report_path, dir_path="/opt/autobug"
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> SliceToolStats:
        self.emit_normal("reading output")
        self.stats.report_stats.generated = 0
        if self.is_file(self.report_path):
            content = self.read_file(self.report_path)
            if len(content) > 0:
                self.stats.report_stats.generated = 1
        return self.stats
