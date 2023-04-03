import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core.utilities import escape_ansi
from app.drivers.tools.AbstractTool import AbstractTool


class FuzzRepair(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(FuzzRepair, self).__init__(self.name)
        self.image_name = "rshariffdeen/fuzzrepair:tool"
        self.bug_id = ""

    def generate_conf_file(self, bug_info):
        repair_conf_path = join(self.dir_setup, "fuzzrepair.conf")
        conf_content = []
        # check there is a file-input defined, if not use default exploit command
        # for example coreutils in vulnloc/extractfix benchmarks have stdarg which are not file inputs
        # instrumentation should convert such to a file argument
        exploit_file_list = bug_info[definitions.KEY_EXPLOIT_LIST]
        if exploit_file_list:
            poc_list = bug_info[definitions.KEY_EXPLOIT_LIST]
            crash_cmd = bug_info[definitions.KEY_CRASH_CMD]
        else:
            poc_list = ["tests/exploit"]
            crash_cmd = ""

        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]
        self.bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[definitions.KEY_BUG_ID]))
        conf_content.append(
            "binary_path:src/{}\n".format(bug_info[definitions.KEY_BINARY_PATH])
        )

        conf_content.append("exploit_command:{}\n".format(crash_cmd))
        conf_content.append(
            "fix_file:{}\n".format(bug_info[definitions.KEY_FIX_FILE]).replace(
                "//", "/"
            )
        )
        conf_content.append("poc:{}\n".format(poc_abs_list[0]))

        # TODO: temp way of only using crash oracle on some bugs
        if "libtiff" in self.dir_expr:
            conf_content.append("only_crash_oracle:1\n")

        self.write_file(conf_content, repair_conf_path)
        return repair_conf_path

    def repair(self, bug_info, config_info):
        super(FuzzRepair, self).repair(bug_info, config_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        timeout_m = str(int(float(timeout_h) * 60))
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        repair_conf_path = self.generate_conf_file(bug_info)
        # repair_conf_path = self.dir_setup + "/crepair/repair.conf"
        self.timestamp_log_start()
        repair_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h ".format(
                str(timeout_h)
            )
        )
        repair_command += " fuzzrepair --conf={0} --time-duration={1} {2}'".format(
            repair_conf_path, str(timeout_m), additional_tool_param
        )

        status = self.run_command(repair_command, log_file_path=self.log_output_path)
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
        tool_log_dir = "/FuzzRepair/logs/"
        tool_log_files = [
            "{}/{}".format(tool_log_dir, f)
            for f in self.list_dir(tool_log_dir)
            if ".log" in f
        ]
        for log_file in tool_log_files:
            copy_command = "cp -rf {} {}".format(log_file, self.dir_output)
            self.run_command(copy_command)
        tool_artifact_dir = "/FuzzRepair/output/"
        tool_artifact_files = [
            "{}/{}".format(tool_artifact_dir, f)
            for f in self.list_dir(tool_artifact_dir)
        ]
        for a_file in tool_artifact_files:
            copy_command = "cp -rf {} {}".format(a_file, self.dir_output)
            self.run_command(copy_command)
        self.run_command(
            "cp -rf /FuzzRepair/output/{} {}".format(self.bug_id, self.dir_output)
        )
        super(FuzzRepair, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)

        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self._space.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = escape_ansi(log_lines[0].rstrip())
            self._time.timestamp_end = escape_ansi(log_lines[-1].rstrip())

            for line in log_lines:
                if "Generating patch" in line:
                    count_plausible += 1
                    count_enumerations += 1
                elif "Runtime Error" in line:
                    self._error.is_error = True
                elif "statistics" in line:
                    is_timeout = False

        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        return self._space, self._time, self._error
