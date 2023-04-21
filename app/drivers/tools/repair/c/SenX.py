import os
import re
from datetime import datetime
from os import listdir
from os.path import isfile
from os.path import join
from typing import cast
from typing import Optional

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SenX(AbstractRepairTool):
    relative_binary_path: Optional[str] = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        self.emit_normal(" instrumenting for " + self.name)
        bug_id = bug_info[self.key_bug_id]
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        buggy_file = bug_info[self.key_fix_file]
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(repair_conf_id, self.name, bug_id),
        )
        time = datetime.now()
        command_str = "bash instrument.sh {}".format(self.dir_expr)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        self.emit_debug(
            "instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        if status not in [0, 126]:
            self.error_exit(
                "error with instrumentation of {}; exit code {}".format(
                    self.name, str(status)
                )
            )
        return

    def run_repair(self, bug_info, repair_config_info):
        super(SenX, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return
        repair_conf_id = repair_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        if not bug_info[self.key_bin_path]:
            self.error_exit("The bug does not have a binary path defined")

        self.relative_binary_path = cast(str, bug_info[self.key_bin_path])
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        binary_dir_path = os.path.dirname(abs_binary_path)
        struct_def_file_path = "def_file"

        test_dir = self.dir_setup + "/tests"
        test_file_list = []
        if self.use_container:
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
        senx_command += binary_input_arg
        senx_command += f" {additional_tool_param} "

        status = self.run_command(
            senx_command,
            dir_path=binary_dir_path,
            log_file_path=self.log_output_path,
        )

        self.process_status(status)
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        copy_command = "cp -rf {}/senx {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        if not self.dir_expr:
            self.error_exit("experiment directory not set")
        if not self.relative_binary_path:
            self.error_exit("relative binary path not set")
        abs_binary_path = join(
            self.dir_expr, "src", cast(str, self.relative_binary_path)
        )
        patch_path = abs_binary_path + ".bc.patch"
        copy_command = "cp -rf {} {}/patches".format(patch_path, self.dir_output)
        self.run_command(copy_command)
        super(SenX, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("[error] no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_error = False

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "Creating patch" in line:
                self._space.plausible += 1
                self._space.enumerations += 1
            elif "Runtime Error" in line:
                self._error.is_error = True
        if is_error:
            self.emit_error("[error] error detected in logs")

        return self._space, self._time, self._error
