import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Hippodrome(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/hippodrome:latest"

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

        # start running
        self.timestamp_log_start()

        run_dir = self.dir_expr
        hippodrome_command = "timeout -k 5m {}h java -jar /hippodrome/target/hippodrome-1.0-jar-with-dependencies.jar -c CONFIG.json".format(
            timeout_h
        )
        if self.is_dir(join(self.dir_expr, "src")):
            hippodrome_command = "timeout -k 5m {}h java -jar /hippodrome/target/hippodrome-1.0-jar-with-dependencies.jar -c ../CONFIG.json".format(
                timeout_h
            )
            run_dir = join(self.dir_expr, "src")

        status = self.run_command(hippodrome_command, self.log_output_path, run_dir)

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

        self.run_command("mkdir -p {}/".format(self.dir_output), "/dev/null", "/")
        self.run_command("cp -rf {} {}/".format(self.dir_expr, self.dir_output))
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
                if "Patch ID:" in line:
                    count = int(line.split(":")[-1])
                    self.stats.patch_stats.plausible = (
                        self.stats.patch_stats.enumerations
                    ) = max(self.stats.patch_stats.generated, count)
                if "Applying Patch ID" in line:
                    self.stats.patch_stats.generated += 1

        return self.stats
