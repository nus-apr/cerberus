import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class PyTER(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "hzhenxin/pyter"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        self.timestamp_log_start()
        self.run_command(f"mkdir -p {join(self.dir_output,'patches')}")
        subject = bug_info.get(self.key_subject, "")
        bug_id = bug_info.get(self.key_bug_id, "")
        src_dir = join(self.dir_expr, "src")
        subject_id = ""
        if bug_id:
            subject_id = bug_id.replace(subject + "-", "")
        benchmark = bug_info.get(self.key_benchmark, "")
        if benchmark == "bugsinpy":
            # Run pyter dynamics for bugsinpy
            self.run_command(
                f"bash /pyter/pyter_tool/dynamic_bugsinpy.sh {src_dir} {bug_id}",
                dir_path=src_dir,
            )

        status = self.run_command(
            'timeout -k 5m {}h python -u pyter_tool/my_tool/main.py -p {} -d {} -b {} -i {} -c ""'.format(
                task_config_info[self.key_timeout],
                subject,
                src_dir,
                benchmark,
                subject_id,
            ),
            self.log_output_path,
            dir_path="/pyter",
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
        self.run_command(
            "bash -c 'cp {}src/result/* {}/'".format(
                self.dir_expr, self.dir_output + "/patches"
            )
        )
        self.run_command(
            "bash -c 'cp -r {}/src/pyter {}/'".format(self.dir_expr, self.dir_output)
        )
        super(PyTER, self).save_artifacts(dir_info)

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

        list_output_dir = self.list_dir(join(self.dir_expr, "src", "result"))
        self.stats.patch_stats.generated = self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".result" in name]
        )

        self.stats.patch_stats.plausible = self.stats.patch_stats.generated

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")

            for line in log_lines:
                if line.startswith("fail"):
                    self.stats.error_stats.is_error = True

        return self.stats