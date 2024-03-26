import json
import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import definitions
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class EvoRepair(AbstractRepairTool):
    evorepair_home = "/opt/EvoRepair"

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/evorepair"
        self.bug_id = ""
        self.hash_digest = (
            "sha256:12bd73e4382acb361ccda3bb333c37e4c44d200ad40ec7fad860d35072f7e952"
        )

    def generate_config_file(self, bug_info: Dict[str, Any]) -> str:
        repair_config_path = os.path.join(self.dir_expr, "src", "repair.json")
        config_object: Dict[str, Dict[str, Any]] = dict()
        config_object["project"] = dict()
        bug_name = bug_info[self.key_bug_id].replace("-", "_").lower()
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
        build_config["commands"]["clean"] = bug_info[self.key_clean_command]
        build_config["commands"]["build"] = bug_info[self.key_build_command]
        config_object["build"] = build_config

        localize_config = dict()
        fix_locations = []
        localization_list = bug_info[self.key_localization]
        for result in localization_list:
            source_file = result[self.key_fix_file]
            line_numbers = result[self.key_fix_lines]
            for _l in line_numbers:
                fix_loc = f"{source_file}:{_l}"
                fix_locations.append(fix_loc)
        localize_config["fix-locations"] = fix_locations
        config_object["localization"] = localize_config

        self.write_file([json.dumps(config_object)], repair_config_path)
        return repair_config_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        repair_config_path = self.generate_config_file(bug_info)
        timeout_h = str(task_config_info[self.key_timeout])
        max_iterations = 2000000
        test_timeout = 30000
        test_partitions = 1
        # generate patches

        self.timestamp_log_start()
        repair_command = (
            f"timeout -k 5m {timeout_h}h evorepair "
            f"--num-iterations {max_iterations} "
            f"--passing-tests-partitions {test_partitions} "
            f"--config {repair_config_path}"
        )

        run_fl = task_config_info[definitions.KEY_CONFIG_FIX_LOC] == "tool"
        if not run_fl:
            repair_command += " --use-given-locations"

        status = self.run_command(
            repair_command, self.log_output_path, self.evorepair_home
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
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

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        self.emit_normal("reading output")

        count_plausible = 0
        count_enumerations = 0
        count_non_compilable = 0
        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
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
        self.stats.patch_stats.generated = len(
            [x for x in self.list_dir(patch_out_dir) if ".diff" in x]
        )
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.non_compilable = count_non_compilable

        return self.stats
