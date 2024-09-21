import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class CrashRepair(AbstractRepairTool):
    error_messages = ["aborted", "core dumped", "runtime error", "segmentation fault"]

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/crashrepair:tool"

    def generate_conf_file(self, bug_info: Dict[str, Any]) -> str:
        repair_conf_path = join(self.dir_setup, "crashrepair", "repair.conf")
        conf_content = []
        if self.key_exploit_list not in bug_info:
            self.error_exit("CrashRepair requires a proof of concept")
        poc_list = bug_info[self.key_exploit_list]
        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]

        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[self.key_bug_id]))
        conf_content.append("src_directory:src\n")
        conf_content.append("binary_path:{}\n".format(bug_info[self.key_bin_path]))
        conf_content.append(
            "config_command:CC=crashrepair-cc CXX=crashrepair-cxx {}\n".format(
                self.dir_setup + "/config.sh " + values.container_base_experiment
            )
        )
        conf_content.append(
            "build_command:CC=crashrepair-cc CXX=crashrepair-cxx {}\n".format(
                self.dir_setup + "/build.sh " + values.container_base_experiment
            )
        )
        if self.key_crash_cmd not in bug_info:
            self.error_exit("CrashRepair requires a test input list")

        conf_content.append("test_input_list:{}\n".format(bug_info[self.key_crash_cmd]))
        conf_content.append("poc_list:{}\n".format(",".join(poc_abs_list)))
        self.append_file(conf_content, repair_conf_path)
        return repair_conf_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        timeout_h = str(task_config_info[self.key_timeout])
        timeout_m = 60 * int(timeout_h)
        timeout_validation = int(timeout_m * 0.75)
        timeout_test = 30
        additional_tool_param = task_config_info[self.key_tool_params]
        patch_limit = 10
        bug_json_path = self.dir_expr + "/bug.json"

        # modify rand_seed for fuzzer
        bug_json_config = self.read_json(bug_json_path)
        if isinstance(bug_json_config, Dict):
            bug_json_config["fuzzer"]["seed"] = int(round(datetime.now().timestamp()))
            self.write_json(bug_json_config, bug_json_path)

        self.timestamp_log_start()
        repair_command = (
            f"bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {str(timeout_h)}h "
            f"crashrepair repair "
            f"--patch-limit {patch_limit} "
            f"--time-limit-minutes-validation {timeout_validation} "
            f"--time-limit-seconds-test {timeout_test} "
            f" {bug_json_path} {additional_tool_param} '"
        )

        status = self.run_command(repair_command, log_file_path=self.log_output_path)

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        tool_log_dir = "/CrashRepair/logs/"
        tool_log_files = [
            "{}/{}".format(tool_log_dir, f)
            for f in self.list_dir(tool_log_dir)
            if ".log" in f
        ]
        list_artifact_dirs = [self.dir_expr + "/" + x for x in ["analysis", "patches"]]
        list_artifact_files = [
            self.dir_expr + "/" + x
            for x in [
                "candidates.json",
                "bug.json",
                "report.json",
                "linter-summary.json",
            ]
        ]
        for f in tool_log_files + list_artifact_files:
            copy_command = f"cp {f} {self.dir_output}"
            self.run_command(copy_command)
        for d in list_artifact_dirs:
            copy_command = f"cp -rf {d} {self.dir_output}"
            self.run_command(copy_command)
        super(CrashRepair, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")

        count_plausible = 0
        count_enumerations = 0
        count_compile_errors = 0
        search_space = 0

        # count number of patch files
        self.stats.patch_stats.generated = len(
            self.list_dir(
                join(
                    self.dir_expr,
                    "patch-valid" if self.use_valkyrie else "patches",
                )
            )
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "evaluating candidate patch" in line:
                    count_enumerations += 1
                if "writing" in line and "mutations" in line:
                    mutations = re.search(r"writing (.*) mutations", line)
                    if not mutations:
                        self.emit_warning("No mutations found??")
                        continue
                    search_space = int(mutations.group(1))
                elif "saving successful patch" in line:
                    count_plausible += 1
                elif "failed to compile" in line:
                    count_compile_errors += 1

                if any(err in line.lower() for err in self.error_messages):
                    self.stats.error_stats.is_error = True

        self.stats.patch_stats.non_compilable = count_compile_errors
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.size = search_space
        return self.stats
