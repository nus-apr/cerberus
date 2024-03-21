import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Recoder(AbstractRepairTool):
    """
    Requirements for this tool:
    15 GB of VRAM, at most 7.0 CUDA (e.g. Nvidia V100) compute and 20 GB of RAM
    """

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "thanhlecong/recoder:v1"
        self.bug_name = ""

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(task_config_info[self.key_timeout])

        if (
            self.key_localization not in bug_info
            or len(bug_info[self.key_localization]) == 0
        ):
            self.error_exit("no line number to fix")

        localization_target = bug_info[self.key_localization][0]

        self.bug_name = bug_info[self.key_bug_id]
        file = (
            join(
                bug_info[self.key_dir_source],
                localization_target[self.key_fix_file].replace(".", "/"),
            )
            + ".java"
        )
        if self.use_gpu:
            recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 inference.py --bug_id {} --class_name {} --buggy_file {} --buggy_line {} --use_gpu'".format(  # currently supporting only defects4j
                timeout_h,
                self.bug_name,
                localization_target[self.key_fix_file],
                join(self.dir_expr, "src", file),
                localization_target[self.key_fix_lines][0],
            )
        else:
            recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 inference.py --bug_id {} --class_name {} --buggy_file {} --buggy_line {}'".format(  # currently supporting only defects4j
                timeout_h,
                self.bug_name,
                localization_target[self.key_fix_file],
                join(self.dir_expr, "src", file),
                localization_target[self.key_fix_lines][0],
            )
        status = self.run_command(
            recorder_command, self.log_output_path, "/root/Repair/"
        )

        recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 validate.py --bug_id {} --patch_info patch/{}-{} --dir {} --buggy_file {}'".format(
            timeout_h,
            self.bug_name,
            bug_info[self.key_subject],
            bug_info[self.key_bug_id],
            join(self.dir_expr, "src"),
            join(self.dir_expr, "src", file),
        )

        status = self.run_command(
            recorder_command,
            self.log_output_path,
            "/root/Repair/",
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
        super().save_artifacts(dir_info)

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

        # count number of patch files
        self.stats.patch_stats.generated = 1

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-3].replace("\n", "")

        if not self.stats.error_stats.is_error:
            self.run_command(
                "cp /root/Repair/patches/{}patch.txt {}/".format(
                    self.bug_name, self.dir_output
                )
            )
            self.stats.patch_stats.generated = 1
            self.stats.patch_stats.enumerations = 1
            self.stats.patch_stats.plausible = 1
            self.stats.patch_stats.non_compilable = 0

        return self.stats
