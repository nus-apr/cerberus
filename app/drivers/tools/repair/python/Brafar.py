import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import container
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Brafar(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "linnaxie/brafar-python"
        self.hash_digest = (
            "sha256:0696fd92a2c918a59c2e51ee1e6f2e00ee260d50fa25b8db3ef41389f356afd2"
        )

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        # print(self.dir_expr)

        self.timestamp_log_start()
        status = self.run_command(
            "timeout -k 5m {}h python3 run.py -d {} -q src -s 100 -o {} {}".format(
                task_config_info[self.key_timeout],
                self.dir_expr,
                "/output/patches",
                task_config_info[self.key_tool_params],
            ),
            self.log_output_path,
            dir_path="/home/linna/brafar-python",
        )
        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        # self.run_command("mkdir /output")
        # self.run_command("mkdir /output/patches")
        # self.run_command("bash -c 'cp {}/src/*.diff /output/patches'".format(self.dir_expr))

        super(Brafar, self).save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """
        # self.stats.patches_stats.non_compilable
        # self.stats.patches_stats.plausible
        # self.stats.patches_stats.size = 1
        # self.stats.patches_stats.enumerations
        # self.stats.patches_stats.generated
        #
        # self.stats.time_stats.total_validation
        # self.stats.time_stats.total_build
        # self.stats.time_stats.timestamp_compilation
        # self.stats.time_stats.timestamp_validation
        # self.stats.time_stats.timestamp_plausible
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_dir(self.dir_patch):
            self.stats.patch_stats.generated = len(self.list_dir(self.dir_patch)) - 1

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.patch_stats.enumerations = 1

            for line in log_lines:
                if line.startswith("fail"):
                    self.stats.error_stats.is_error = True
                if line.startswith("The repair result is:"):
                    if "True" in line:
                        self.stats.patch_stats.plausible += 1
                    elif "False" in line:
                        self.stats.patch_stats.generated += 1
                        self.stats.patch_stats.enumerations += 1

        return self.stats
