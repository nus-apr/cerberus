import json
import os
import re
from os.path import join
from typing import Any
from typing import Dict

from app.core import definitions
from app.core import emitter
from app.core import values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class EvoRepair(AbstractRepairTool):

    evorepair_home = "/opt/EvoRepair"

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(EvoRepair, self).__init__(self.name)
        self.image_name = "rshariffdeen/evorepair"
        self.bug_id = ""

    def generate_config_file(self, bug_info):
        repair_config_path = os.path.join(self.dir_expr, "src", "repair.json")
        config_object: Dict[str, Dict[str, Any]] = dict()
        config_object["project"] = dict()
        subject_name = bug_info[definitions.KEY_SUBJECT]
        bug_id = bug_info[definitions.KEY_BUG_ID]
        bug_name = f"{subject_name.lower()}_{bug_id}"
        self.bug_id = bug_name
        config_object["project"]["name"] = bug_name
        config_object["project"]["tag"] = bug_name

        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])
        list_deps = bug_info["dependencies"]
        dir_java_deps = f"{self.dir_expr}/deps"
        for dep in list_deps:
            if "src" == dep[:3]:
                dir_java_deps = dep[4:].split("/")[0]
                break

        config_object["project"]["source-directory"] = dir_java_src
        config_object["project"]["test-directory"] = dir_test_bin
        config_object["project"]["deps-directory"] = dir_java_deps
        config_object["project"]["class-directory"] = dir_java_bin

        build_config: Dict[str, Any] = dict()
        build_config["directory"] = os.path.join(self.dir_expr, "src")
        build_config["commands"] = dict()
        build_config["commands"]["pre-build"] = "exit 0"
        build_config["commands"]["clean"] = "rm -rf build build-tests"
        build_config["commands"]["build"] = "defects4j compile"
        config_object["build"] = build_config

        localize_config = dict()
        localize_config["fix-locations"] = [bug_info[definitions.KEY_FIX_LOC]]
        config_object["localization"] = localize_config

        self.write_file(json.dumps(config_object), repair_config_path)
        return repair_config_path

    def run_repair(self, bug_info, config_info):
        super(EvoRepair, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        repair_config_path = self.generate_config_file(bug_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        max_iterations = 2000000
        test_timeout = 30000
        test_partitions = 1
        # generate patches
        self.timestamp_log_start()
        repair_command = (
            f"timeout -v -k 5m {timeout_h}h evorepair "
            f"--num-iterations {max_iterations} "
            f"--passing-tests-partitions {test_partitions} "
            f"--config {repair_config_path}"
        )

        status = self.run_command(
            repair_command, self.log_output_path, self.evorepair_home
        )

        self.process_status(status)

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        tool_log_dir = f"{self.evorepair_home}/logs/{self.bug_id}"
        tool_log_files = [f for f in self.list_dir(tool_log_dir)]
        for log_file in tool_log_files:
            copy_command = "cp -rf {} {}".format(log_file, self.dir_output)
            self.run_command(copy_command)

        tool_artifact_dir = f"{self.evorepair_home}/output/"
        tool_artifact_files = [f for f in self.list_dir(tool_artifact_dir)]
        for a_file in tool_artifact_files:
            copy_command = "cp -rf {} {}".format(a_file, self.dir_output)
            self.run_command(copy_command)
        super(EvoRepair, self).save_artifacts(dir_info)

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

        count_plausible = 0
        count_enumerations = 0
        count_non_compilable = 0
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
                if "total patches that pass all user tests" in line.lower():
                    # new_count = int(
                    #     str(re.search(r"got (.*) patches", line).group(1)).strip()
                    # )
                    count_plausible = int(line.split(":")[-1])
                elif "total patches that pass failing user tests" in line.lower():
                    count_enumerations = int(line.split(":")[-1])
                elif "because compilation failed" in line:
                    count_non_compilable += 1

        tool_out_dir = self.evorepair_home + "/output"
        exp_out_dir = f"{tool_out_dir}/{self.list_dir(tool_out_dir)[0]}"
        patch_out_dir = f"{exp_out_dir}/perfect-patches"
        self._space.generated = len(
            [x for x in self.list_dir(patch_out_dir) if ".diff" in x]
        )
        self._space.enumerations = count_enumerations
        self._space.plausible = count_plausible
        self._space.non_compilable = count_non_compilable

        return self._space, self._time, self._error
