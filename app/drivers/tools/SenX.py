import os
import re
from datetime import datetime
from os import listdir
from os.path import isfile
from os.path import join
from typing import Optional

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.core.utilities import execute_command
from app.drivers.tools.AbstractTool import AbstractTool


class SenX(AbstractTool):
    relative_binary_path: Optional[str] = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(SenX, self).__init__(self.name)

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.current_profile_id)
        buggy_file = bug_info[definitions.KEY_FIX_FILE]
        self.log_instrument_path = join(
            self.dir_logs, "{}-{}-{}-instrument.log".format(conf_id, self.name, bug_id)
        )
        time = datetime.now()
        command_str = "bash instrument.sh {}".format(self.dir_expr)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        emitter.debug(
            "\t\t\t Instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of {}; exit code {}".format(
                    self.name, str(status)
                )
            )
        return

    def repair(self, bug_info, config_info):
        super(SenX, self).repair(bug_info, config_info)
        if values.only_instrument:
            return
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )

        self.relative_binary_path = bug_info[definitions.KEY_BINARY_PATH]
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        binary_dir_path = os.path.dirname(abs_binary_path)
        struct_def_file_path = "def_file"

        test_dir = self.dir_setup + "/tests"
        test_file_list = []
        if values.use_container:
            emitter.error(
                "[Exception] unimplemented functionality: SenX docker support not implemented"
            )
            error_exit("Unhandled Exception")
        else:
            if os.path.isdir(test_dir):
                test_file_list = [
                    join(test_dir, f)
                    for f in listdir(test_dir)
                    if isfile(join(test_dir, f))
                ]

        if len(test_file_list) > 1:
            emitter.warning(
                "\t\t(warning) unimplemented functionality: SenX only supports one failing test-case"
            )

        binary_input_arg = bug_info[definitions.KEY_CRASH_CMD]
        if "$POC" in binary_input_arg:
            binary_input_arg = binary_input_arg.replace("$POC", test_file_list[0])
        self.timestamp_log_start()
        senx_command = "cd {};".format(binary_dir_path)
        senx_command += "timeout -k 5m {0}h senx -struct-def={2} {1}.bc ".format(
            str(timeout_h),
            self.relative_binary_path.split("/")[-1],
            struct_def_file_path,
        )
        senx_command += binary_input_arg
        senx_command += "{0} >> {1} 2>&1 ".format(
            additional_tool_param, self.log_output_path
        )
        status = execute_command(senx_command)
        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        copy_command = "cp -rf {}/senx {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        if not (self.dir_expr and self.relative_binary_path):
            error_exit("Unset paths in setup for SenX")
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        patch_path = abs_binary_path + ".bc.patch"
        copy_command = "cp -rf {} {}/patches".format(patch_path, self.dir_output)
        self.run_command(copy_command)
        super(SenX, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id)
        self.log_analysis_path = join(
            self.dir_logs,
            "{}-{}-{}-analysis.log".format(conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
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
            emitter.error("\t\t\t\t(error) error detected in logs")

        return self._space, self._time, self._error
