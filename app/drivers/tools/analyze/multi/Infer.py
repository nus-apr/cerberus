import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.AnalysisToolStats import AnalysisToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class Infer(AbstractAnalyzeTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK",
        "Use After Free": "USE_AFTER_FREE",
        "Double Free": "DOUBLE_FREE",
    }

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        # the version in ubuntu-18 as better compatibility with the VulnLoc benchmark
        self.image_name = "yuntongzhang/infer:facebook-ubuntu-18"

    def pre_process(self, bug_info: Dict[str, Any]) -> None:
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)

        self.emit_normal("preparing subject for analysis")
        dir_src = join(self.dir_expr, "src")
        env = {}
        if bug_info.get(self.key_language, "") == "java":
            env["JAVA_HOME"] = "/usr/lib/jvm/java-{}-openjdk-amd64".format(
                bug_info.get("java_version", 8)
            )
            if int(bug_info.get("java_version", 8)) == 8:
                self.run_command(
                    f"update-java-alternatives -s java-1.8.0-openjdk-amd64"
                )

        clean_command = bug_info.get(self.key_clean_command, "make clean")
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        # this build command is for the VulnLoc benchmark;
        # to support other benchmarks, look at the meta-data.json file in VulnLoc
        build_cmd = bug_info.get(self.key_build_command, "")
        config_cmd = bug_info.get(self.key_config_command, "")
        if config_cmd:
            infer_command = f"infer capture -- {config_cmd}"
            self.run_command(infer_command, dir_path=dir_src)

        log_compile_path = join(self.dir_logs, "infer-compile-output.log")
        compile_command = "infer capture -- {}".format(build_cmd)

        if bug_info.get(self.key_language, "") == "java":
            compile_command = "infer capture --java-version {} -- {}".format(
                bug_info.get("java_version", 8), build_cmd
            )

        self.emit_normal("compiling subject with ")
        status = self.run_command(
            compile_command, dir_path=dir_src, log_file_path=log_compile_path, env=env
        )
        if status != 0:
            self.emit_error("infer capture command returned non-zero exit")
        self.emit_normal(
            "compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]

        self.timestamp_log_start()
        dir_src = join(self.dir_expr, "src")
        # add --keep-going to not abort when having runtime errors
        analysis_command = "infer analyze {} --keep-going".format(additional_tool_param)

        status = self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=self.log_output_path
        )
        if status != 0:
            self.emit_error("infer analyze command returned non-zero exit")

        self.process_status(status)

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        infer_output = join(self.dir_expr, "src", "infer-out")
        infer_report_json = join(infer_output, "report.json")
        infer_report_txt = join(infer_output, "report.txt")
        copy_command_json = "cp -f {} {}".format(infer_report_json, self.dir_output)
        copy_command_txt = "cp -f {} {}".format(infer_report_txt, self.dir_output)
        self.run_command(copy_command_json)
        self.run_command(copy_command_txt)
        super(Infer, self).save_artifacts(dir_info)
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
            if "ERROR:" in line:
                is_error = True
                self.stats.error_stats.is_error = True
        if is_error:
            self.emit_error("error detected in logs")
        return self.stats
