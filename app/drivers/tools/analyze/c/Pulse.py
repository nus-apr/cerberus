import os
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.AnalysisToolStats import AnalysisToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class Pulse(AbstractAnalyzeTool):
    relative_binary_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "yuntongzhang/infer:v2"

    def pre_process(self, bug_info: Dict[str, Any]) -> None:
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        self.emit_normal("preparing subject for analysis with " + self.name)
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        bug_id = str(bug_info[self.key_bug_id])
        self.log_prepare_path = join(
            self.dir_logs,
            "{}-{}-prepare.log".format(self.name.lower(), bug_id),
        )

        compile_list = bug_info.get(self.key_compile_programs, [])
        compile_command = "infer -j 20 capture -- make -j20 {}".format(
            " ".join(compile_list)
        )
        self.emit_normal("compiling subject with " + self.name)
        status = self.run_command(
            compile_command, dir_path=dir_src, log_file_path=self.log_prepare_path
        )
        if status != 0:
            self.emit_error("pulse capture command returned non-zero exit")

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
        max_disjuncts = 20
        analysis_command = (
            f"timeout -k 5m {str(timeout_h)}h infer --pulse-only "
            f" --pulse-max-disjuncts {max_disjuncts} "
            f" --scheduler callgraph {additional_tool_param} "
        )

        dir_src = join(self.dir_expr, "src")
        status = self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=self.log_output_path
        )
        if status != 0:
            self.emit_error("pulse analyze command returned non-zero exit")

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        infer_output = join(self.dir_expr, "src", "infer-out")
        copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        self.run_command(copy_command)
        super(Pulse, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> AnalysisToolStats:
        self.emit_normal("reading output")
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
