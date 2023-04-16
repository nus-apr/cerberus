import os
import re
from datetime import datetime
from os.path import join

from app.core.utilities import error_exit
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class SAVER(AbstractAnalyzeTool):
    relative_binary_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success preparing subject for repair with "
            + self.name
        )
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        bug_type = bug_info[self.key_bug_type]
        if bug_type == "Memory Leak":
            compile_command = (
                "infer -j 20 -g --headers --check-nullable-only -- make -j20"
            )
        else:
            compile_command = (
                "infer -j 20 run -g --headers --check-nullable-only -- make -j20"
            )
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successself.emit_success compiling subject with "
            + self.name
        )
        self.run_command(compile_command, dir_path=dir_src)
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successself.emit_success compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def run_analysis(self, bug_info, config_info):
        self.prepare(bug_info)
        super(SAVER, self).run_analysis(bug_info, config_info)
        if self.is_instrument_only:
            return
        timeout_h = str(config_info[self.key_timeout])
        additional_tool_param = config_info[self.key_tool_params]

        if values.use_container:
            self.emit_error(
                "[Exception] unimplemented functionality: SAVER docker support not implemented"
            )
            error_exit("Unhandled Exception")

        self.timestamp_log_start()
        bug_type = bug_info[self.key_bug_type]
        dir_src = join(self.dir_expr, "src")
        saver_command = "timeout -k 5m {0}h infer saver --pre-analysis-only {1}".format(
            str(timeout_h), additional_tool_param
        )

        status = self.run_command(
            saver_command, dir_path=dir_src, log_file_path=self.log_output_path
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight(
            "self.emit_successself.emit_successself.emit_successlog file: {0}".format(
                self.log_output_path
            )
        )

    def save_artifacts(self, dir_info):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success saving artifacts of "
            + self.name
        )
        copy_command = "cp -rf {}/saver {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        infer_output = join(self.dir_expr, "src", "infer-out")
        copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        self.run_command(copy_command)
        super(SAVER, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        conf_id = str(self.current_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(
            "self.emit_successself.emit_successself.emit_success Log File: "
            + self.log_output_path
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
