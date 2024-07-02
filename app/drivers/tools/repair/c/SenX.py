import os
import re
from datetime import datetime
from os import listdir
from os.path import isfile
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SenX(AbstractRepairTool):
    relative_binary_path: Optional[str] = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        if self.is_instrument_only:
            return
        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        if not bug_info[self.key_bin_path]:
            self.error_exit("The bug does not have a binary path defined")

        self.relative_binary_path = cast(str, bug_info[self.key_bin_path])
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        binary_dir_path = os.path.dirname(abs_binary_path)
        struct_def_file_path = "def_file"

        test_dir = self.dir_setup + "/tests"
        test_file_list = []
        if self.use_container and not self.locally_running:
            self.error_exit(
                "unimplemented functionality: SenX docker support not implemented"
            )
        else:
            if os.path.isdir(test_dir):
                test_file_list = [
                    join(test_dir, f)
                    for f in listdir(test_dir)
                    if isfile(join(test_dir, f))
                ]

        if len(test_file_list) > 1:
            self.emit_warning(
                "[error] unimplemented functionality: SenX only supports one failing test-case"
            )

        binary_input_arg = bug_info[self.key_crash_cmd]
        if "$POC" in binary_input_arg:
            binary_input_arg = binary_input_arg.replace("$POC", test_file_list[0])
        self.timestamp_log_start()
        senx_command = "timeout -k 5m {0}h senx -struct-def={2} {1}.bc ".format(
            str(timeout_h),
            self.relative_binary_path.split("/")[-1],
            struct_def_file_path,
        )

        senx_command += f" {binary_input_arg} {additional_tool_param} "
        dir_src = join(self.dir_expr, "src")
        status = self.run_command(
            senx_command,
            dir_path=dir_src,
            log_file_path=self.log_output_path,
        )

        self.process_status(status)
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        copy_command = "cp -rf {}/senx {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        if not self.dir_expr:
            self.error_exit("experiment directory not set")
        if not self.relative_binary_path:
            self.error_exit("relative binary path not set")
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        patch_path = abs_binary_path + ".bc.patch"
        copy_command = "cp -rf {} {}/patches".format(patch_path, self.dir_output)
        self.run_command(copy_command)
        super(SenX, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("[error] no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_error = False

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "Creating patch" in line:
                self.stats.patch_stats.plausible += 1
                self.stats.patch_stats.enumerations += 1
            elif "Runtime Error" in line:
                is_error = True
                self.stats.error_stats.is_error = True
        if is_error:
            self.emit_error("[error] error detected in logs")

        return self.stats
