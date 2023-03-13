import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class VulnFix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(VulnFix, self).__init__(self.name)
        self.dir_root = "/home/yuntong/vulnfix"
        self.image_name = "yuntongzhang/vulnfix:latest"

    def repair(self, bug_info, config_info):
        super(VulnFix, self).repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """
        if values.only_instrument:
            return

        dir_vulnfix_exist = self.is_dir(self.dir_root)
        if not dir_vulnfix_exist:
            emitter.error(
                "[Exception] Vulnfix repo is not at the expected location. "
                "Please double check whether we are in VulnFix container."
            )
            error_exit("Unhandled exception")
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        # get ready the config file
        config_path = self.populate_config_file(bug_info)

        # start running
        self.timestamp_log_start()
        vulnfix_command = "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h vulnfix {1} {2}'".format(
            timeout_h, additional_tool_param, config_path
        )
        status = self.run_command(
            vulnfix_command, log_file_path=self.log_output_path, dir_path=self.dir_root
        )

        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def populate_config_file(self, bug_info):
        """
        Some fields of the VulnFix config file contains information which overlaps with what
        Cerberus already has, and also some of the fields depends on actual paths in the system. These fields are populated here into the existing config file template.
        """
        # the config template should have been copied here
        config_path = join(self.dir_expr, "vulnfix", "config")

        # first check whether config already has a cmd line;
        # this is because vulnfix sometimes instrument program for AFL argv fuzzing, which
        # changes the command for invoking the program
        orig_config_lines = self.read_file(config_path)
        cmd_already_specified = False
        binary_already_specified = False
        for config_line in orig_config_lines:
            config_type = config_line.split("=")[0]
            if config_type == "cmd":
                cmd_already_specified = True
            if config_type == "binary":
                binary_already_specified = True

        # (1) source-dir
        dir_src = join(self.dir_expr, "src")
        line_source_dir = "source-dir=" + dir_src + "\n"
        # (2) binary
        rel_binary_path = bug_info[definitions.KEY_BINARY_PATH]
        binary_path = join(dir_src, rel_binary_path)
        line_binary = "binary=" + binary_path + "\n"
        # (3) (OPTIONAL) cmd
        line_cmd = ""
        if not cmd_already_specified:
            cmd = bug_info[definitions.KEY_CRASH_CMD]
            cmd = cmd.replace("$POC", "<exploit>")
            line_cmd = "cmd=" + cmd + "\n"
        # (4) exploit

        if (
            definitions.KEY_EXPLOIT_LIST not in bug_info
            or len(bug_info[definitions.KEY_EXPLOIT_LIST]) < 1
        ):
            # assumes instrumentation converted stdarg as a file handling command
            exploit_path = join(self.dir_setup, "tests/exploit")
        else:
            exploit_path = join(
                self.dir_setup, sorted(bug_info[definitions.KEY_EXPLOIT_LIST])[0]
            )
        line_exploit = "exploit=" + exploit_path + "\n"
        # (5) (OPTIONAL) normal-in
        line_normals = ""
        dir_normal_in = join(self.dir_setup, "vulnfix", "normals")
        normals_list = self.list_dir(dir_normal_in)
        if normals_list:
            line_normals = "normal-in=" + ",".join(normals_list) + "\n"

        # (6) runtime-dir
        line_runtime_dir = "runtime-dir=" + self.dir_output + "\n"

        self.run_command("mkdir -p {}/afl-out/crashes".format(self.dir_output))

        config_updates = list()
        if not binary_already_specified:
            config_updates.append(line_binary)
        if line_cmd:
            config_updates.append(line_cmd)
        config_updates.append(line_exploit)
        if line_normals:
            config_updates.append(line_normals)
        config_updates.append(line_runtime_dir)
        config_updates.append(line_source_dir)
        self.append_file(config_updates, config_path)
        return config_path

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self._space.non_compilable
            self._space.plausible
            self._space.size
            self._space.enumerations
            self._space.generated

            self._time.total_validation
            self._time.total_build
            self._time.timestamp_compilation
            self._time.timestamp_validation
            self._time.timestamp_plausible
        """
        emitter.normal("\t\t\t analysing output of " + self.name)

        is_error = False
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
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")

            for line in log_lines:
                if "Generating patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        self._error.is_error = is_error
        return self._space, self._time, self._error
