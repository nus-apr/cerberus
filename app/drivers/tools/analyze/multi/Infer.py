import os
import re
from datetime import datetime
from os.path import join

from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class Infer(AbstractAnalyzeTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK",
        "Use After Free": "USE_AFTER_FREE",
        "Double Free": "DOUBLE_FREE",
    }

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "yuntongzhang/infer:latest"

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)

        self.emit_normal("preparing subject for analysis")
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        compile_list = bug_info.get(self.key_compile_programs, [])
        log_compile_path = join(self.dir_logs, "infer-compile-output.log")
        compile_command = "infer -j 20 -g capture -- make -j20 {}".format(
            " ".join(compile_list)
        )

        self.emit_normal("compiling subject with ")
        status = self.run_command(
            compile_command, dir_path=dir_src, log_file_path=log_compile_path
        )
        if status != 0:
            self.emit_error("infer capture command returned non-zero exit")
        self.emit_normal(
            "compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def run_analysis(self, bug_info, repair_config_info):
        self.prepare(bug_info)
        super(Infer, self).run_analysis(bug_info, repair_config_info)
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]

        self.timestamp_log_start()
        dir_src = join(self.dir_expr, "src")
        compile_list = bug_info.get(self.key_compile_programs, [])
        saver_command = "timeout -k 5m {0}h infer analyze {1} -- make -j20 {2}".format(
            str(timeout_h), additional_tool_param, " ".join(compile_list)
        )

        status = self.run_command(
            saver_command, dir_path=dir_src, log_file_path=self.log_output_path
        )
        if status != 0:
            self.emit_error("infer analyze command returned non-zero exit")

        self.process_status(status)

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        infer_output = join(self.dir_expr, "src", "infer-out")
        copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        self.run_command(copy_command)
        super(Infer, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output logs")
        dir_results = join(self.dir_expr, "result")
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(repair_conf_id, self.name.lower(), bug_id),
        )
        is_error = False
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "ERROR:" in line:
                self._error.is_error = True
        if is_error:
            self.emit_error("error detected in logs")
        return self._space, self._time, self._error
