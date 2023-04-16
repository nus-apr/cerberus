import os
import re
from datetime import datetime
from os.path import join

from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class Hippodrome(AbstractAnalyzeTool):
    def __init__(self):
        super().__init__(self.name)
        self.image_name = "mirchevmp/hippodrome:latest"

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success preparing subject for analysis with "
            + self.name
        )
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        bug_type = bug_info[definitions.KEY_BUG_TYPE]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.log_prepare_path = join(
            self.dir_logs,
            "{}-{}-prepare.log".format(self.name.lower(), bug_id),
        )
        compile_command = "infer -j 20 compile -- make -j20"
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successself.emit_success compiling subject with "
            + self.name
        )
        self.run_command(
            compile_command, dir_path=dir_src, log_file_path=self.log_prepare_path
        )
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successself.emit_success compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def run_analysis(self, bug_info, config_info):
        super(Hippodrome, self).run_analysis(bug_info, config_info)
        self.prepare(bug_info)
        super(Hippodrome, self).run_analysis(bug_info, config_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]

        self.timestamp_log_start()
        analysis_command = (
            "timeout -k 5m {0}h infer "
            " --racerdfix-only --starvation --no-deduplicate {1} ".format(
                str(timeout_h), additional_tool_param
            )
        )
        bug_type = bug_info[definitions.KEY_BUG_TYPE]
        dir_src = join(self.dir_expr, "src")
        status = self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=self.log_output_path
        )

        self.process_status(status)

        self.emit_highlight(
            "self.emit_successself.emit_successself.emit_successlog file: {0}".format(
                self.log_output_path
            )
        )
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success saving artifacts of "
            + self.name
        )
        infer_output = join(self.dir_expr, "src", "infer-out")
        copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        self.run_command(copy_command)
        super(Hippodrome, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(conf_id, self.name.lower(), bug_id),
        )
        is_error = False
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "ERROR:" in line:
                self._error.is_error = True
        if is_error:
            self.emit_error(
                "self.emit_successself.emit_successself.emit_successself.emit_success[error] error detected in logs"
            )

        return self._space, self._time, self._error
