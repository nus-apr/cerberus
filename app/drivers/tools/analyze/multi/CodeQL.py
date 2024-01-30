import os
import re
from datetime import datetime
from os.path import join

from app.core import values
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class CodeQL(AbstractAnalyzeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # the version in ubuntu-18 as better compatibility with the VulnLoc benchmark
        self.image_name = "mirchevmp/codeql-docker"
        self.runs_as_root = False
        self.image_user = "ubuntu"
        self.sudo_password = "ubuntu"
        self.bindings = {
            values.dir_dynamic: {
                "bind": "/queries",
                "mode": "rw",
            }
        }

    def run_analysis(self, bug_info, repair_config_info):
        super(CodeQL, self).run_analysis(bug_info, repair_config_info)
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]

        self.timestamp_log_start()
        dir_src = join(self.dir_expr, "src")
        language = bug_info.get(self.key_language, "all")

        self.write_json([bug_info], os.path.join(self.dir_expr, "meta-data.json"))

        analysis_command = (
            "bash /home/ubuntu/workspace/script/cerberus_entrypoint.sh {} {}".format(
                os.path.join(self.dir_expr, "meta-data.json"), language
            )
        )

        status = self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=self.log_output_path
        )

        self.process_status(status)

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        # infer_output = join(self.dir_expr, "src", "infer-out")
        # infer_report_json = join(infer_output, "report.json")
        # infer_report_txt = join(infer_output, "report.txt")
        # copy_command_json = "cp -f {} {}".format(infer_report_json, self.dir_output)
        # copy_command_txt = "cp -f {} {}".format(infer_report_txt, self.dir_output)
        # self.run_command(copy_command_json)
        # self.run_command(copy_command_txt)
        super(CodeQL, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output logs")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        is_error = False
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "ERROR" in line:
                is_error = True
                self.stats.error_stats.is_error = True
        if is_error:
            self.emit_error("error detected in logs")
        return self.stats
