import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.AnalysisToolStats import AnalysisToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class CodeQL(AbstractAnalyzeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # the version in ubuntu-18 as better compatibility with the VulnLoc benchmark
        self.image_name = "mirchevmp/codeql-docker"
        self.runs_as_root = False
        self.image_user = "ubuntu"
        self.sudo_password = "ubuntu"
        os.makedirs(join(values.dir_dynamic, "codeql_queries"), exist_ok=True)
        self.bindings = {
            join(values.dir_dynamic, "codeql_queries"): {
                "bind": "/queries",
                "mode": "rw",
            }
        }

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]

        self.timestamp_log_start()
        dir_src = join(self.dir_expr, "src")
        language = bug_info.get(self.key_language, "all")
        if language == "c":
            # Ensure that the project is clean and can be built
            self.run_command("make clean", dir_path=join(self.dir_expr, "src"))
            language = "cpp"  # Expand c to cpp

        metadata_loc = os.path.join(self.dir_expr, "meta-data.json")

        self.write_json([bug_info], metadata_loc)

        self.run_command(
            "bash -c 'echo \"{}\n\" | sudo -S mkdir -p {}'".format(
                self.sudo_password, self.dir_output
            )
        )
        self.output_path = join(
            "/home",
            "ubuntu",
            "workspace",
            "output",
            bug_info[self.key_benchmark],
            bug_info[self.key_subject],
            bug_info[self.key_bug_id],
        )

        analysis_command = (
            "bash /home/ubuntu/workspace/script/cerberus_entrypoint.sh {} {}".format(
                metadata_loc, language
            )
        )

        status = self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=self.log_output_path
        )

        self.process_status(status)

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        self.run_command(
            "bash -c 'echo \"{}\n\" | sudo -S cp {}/* {}'".format(
                self.sudo_password, self.output_path, self.dir_output
            )
        )
        super(CodeQL, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> AnalysisToolStats:
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
