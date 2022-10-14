import os
import shutil
import re
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container
from os import listdir
from os.path import isfile, join


class FuzzRepair(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(FuzzRepair, self).__init__(self.name)
        self.image_name="rshariffdeen/fuzzrepair:tool"

    def generate_conf_file(self, bug_info):
        repair_conf_path = join(self.dir_setup,"fuzzrepair.conf")
        conf_content = []
        poc_list = bug_info[definitions.KEY_EXPLOIT_LIST]
        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]

        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[definitions.KEY_BUG_ID]))
        conf_content.append(
            "binary_path:src/{}\n".format(bug_info[definitions.KEY_BINARY_PATH])
        )

        conf_content.append(
            "exploit_command:{}\n".format(bug_info[definitions.KEY_CRASH_CMD])
        )
        conf_content.append("poc:{}\n".format(poc_abs_list[0]))
        self.append_file(conf_content, repair_conf_path)
        return repair_conf_path

    def repair(self, bug_info, config_info):
        super(FuzzRepair, self).repair(bug_info, config_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        repair_conf_path = self.generate_conf_file(bug_info)
        # repair_conf_path = self.dir_setup + "/crepair/repair.conf"
        self.timestamp_log()
        repair_command = "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h fuzzrepair --conf={1} {2}'".format(
            str(timeout_h), repair_conf_path, additional_tool_param
        )
        status = self.run_command(repair_command, log_file_path=self.log_output_path)
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
        tool_log_dir = "/FuzzRepair/logs/"
        tool_log_files = [
            "{}/{}".format(tool_log_dir, f)
            for f in self.list_dir(tool_log_dir)
            if ".log" in f
        ]
        for log_file in tool_log_files:
            copy_command = "cp {} {}".format(log_file, self.dir_output)
            self.run_command(copy_command)
        tool_artifact_dir = "/FuzzRepair/output/"
        tool_artifact_files = [
            "{}/{}".format(tool_artifact_dir, f)
            for f in self.list_dir(tool_artifact_dir)
        ]
        for a_file in tool_artifact_files:
            copy_command = "cp {} {}".format(a_file, self.dir_output)
            self.run_command(copy_command)
        super(FuzzRepair, self).save_artefacts(dir_info)
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
            emitter.warning("\t\t\t[warning] no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "Generating patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        return self._space, self._time, self._error