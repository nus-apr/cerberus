import os
import re
from drivers.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
from os import listdir
from os.path import isfile, join


class SenX(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(SenX, self).__init__(self.name)
        self.relative_binary_path

    def repair(self, bug_info, config_info):
        super(SenX, self).repair(bug_info, config_info)
        if values.CONF_INSTRUMENT_ONLY:
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
        binary_dir_path = join(*abs_binary_path.split("/")[:-1])
        struct_def_file_path = "def_file"

        test_dir = self.dir_setup + "/tests"
        test_file_list = []
        if values.CONF_USE_CONTAINER:
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
                "\t\t[warning] unimplemented functionality: SenX only supports one failing test-case"
            )

        binary_input_arg = bug_info[definitions.KEY_CRASH_CMD]
        if "$POC" in binary_input_arg:
            binary_input_arg = binary_input_arg.replace("$POC", test_file_list[0])
        self.timestamp_log()
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
                "\t\t\t[warning] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        self.timestamp_log()

    def save_artefacts(self, dir_info):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        copy_command = "cp -rf {}/senx {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        abs_binary_path = join(self.dir_expr, "src", self.relative_binary_path)
        patch_path = abs_binary_path + ".bc.patch"
        copy_command = "cp -rf {} {}/patches".format(patch_path, self.dir_output)
        self.run_command(copy_command)
        super(SenX, self).save_artefacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.CONFIG_ID)
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
            emitter.warning("\t\t\t[warning] no output log file found")
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
            emitter.error("\t\t\t\t[error] error detected in logs")

        return self._space, self._time, self._error
