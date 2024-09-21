import os
from os import path
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class AICCModel(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/aiccm"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        if self.is_instrument_only:
            return

        # modify the output directory as it depends on the experiment
        self.dir_output = path.join(self.dir_expr, "result")
        self.dir_logs = path.join(self.dir_expr, "logs")

        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        # prepare the config file

        # start running
        self.timestamp_log_start()
        tool_commandd = "bash -c 'source /ExtractFix/setup.sh && timeout -k 5m {}h ./ExtractFix.py {} {} >> {}'".format(
            timeout_h, "", additional_tool_param, self.log_output_path
        )
        status = self.run_command(
            tool_commandd,
            log_file_path=self.log_output_path,
            dir_path=path.join(self.dir_expr, "src"),
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
        return

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

        is_error = False
        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if "patch" in name]
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

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.error_stats.is_error = is_error
        return self.stats
