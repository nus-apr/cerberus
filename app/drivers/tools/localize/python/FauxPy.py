import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class FauxPy(AbstractLocalizeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/fauxpy:latest"

    def generate_meta_data(self, localization_file_path: str) -> None:
        localization = []
        lines = self.read_file(localization_file_path)[1:]
        for entry in lines:
            src_loc, score = entry.split(",")
            source_file, line_number = src_loc.split("::")
            localization.append(
                {
                    "source_file": source_file,
                    "line_numbers": [line_number],
                    "score": score,
                }
            )
        new_metadata = {
            self.key_analysis_output: [
                {
                    "generator": self.name,
                    "confidence": 1,
                    "localization": localization,
                }
            ]
        }
        self.write_json([new_metadata], join(self.dir_output, "meta-data.json"))

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        additional_tool_param = task_config_info[self.key_tool_params]

        self.timestamp_log_start()
        localize_command = 'bash -c \'timeout -k 5m {}h python3 -m pytest --src . --family sbfl {} --exclude "[$(ls | grep test | grep .py | tr "\\n" "," | sed "s/,$//")]"\''.format(
            timeout,
            additional_tool_param,
        )

        formula = bug_info.get("fl_formula", "Ochiai")

        status = self.run_command(
            localize_command, self.log_output_path, dir_path=join(self.dir_expr, "src")
        )

        localization_file_path = join(self.dir_output, "localization.csv")
        if status == 1:
            # The test suite has failing tests but this is generally what we want to so we change the code to success if the report is generated
            report_list = self.list_dir(join(self.dir_expr), regex="FauxPyReport*")
            if len(report_list) > 0:
                self.run_command(
                    "bash -c 'cp -r {} {}'".format(report_list[0], self.dir_output),
                    dir_path=self.dir_expr,
                )
                self.run_command(
                    "bash -c 'cp {}/Scores_{}.csv {}'  ".format(
                        report_list[0],
                        formula,
                        localization_file_path,
                    ),
                    dir_path=self.dir_expr,
                )
                status = 0
        if self.is_file(localization_file_path):
            self.generate_meta_data(localization_file_path)
        self.process_status(status)
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        output_file = join(self.dir_output, "localization.csv")
        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "statistics" in line:
                    is_timeout = False
        if self.is_file(output_file):
            output_lines = self.read_file(output_file, encoding="iso-8859-1")[1:]
            unique_src_list = set()
            for result in output_lines:
                src_loc, score = result.split(",")
                source_file, line_number = src_loc.split("::")
                unique_src_list.add(source_file)
            self.stats.fix_loc_stats.source_files = len(unique_src_list)
            self.stats.fix_loc_stats.fix_locs = len(output_lines)
        else:
            self.emit_error("no output file found")
            self.stats.error_stats.is_error = True

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
