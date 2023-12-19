import os
import re
from os.path import join

from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class E9PatchSBFL(AbstractLocalizeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/sbfl-e9patch:latest"
        self.id = ""

    def run_localization(self, bug_info, localization_config_info):
        super(E9PatchSBFL, self).run_localization(bug_info, localization_config_info)
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(localization_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = localization_config_info[self.key_tool_params]

        if self.key_bin_path not in bug_info:
            self.emit_error("No binary path found")

        self.timestamp_log_start()

        self.emit_normal("Instrumenting binary")

        lines = len(
            self.read_file(
                join(self.dir_expr, "src", bug_info[self.key_fix_file]),
                encoding="iso-8859-1",
            )
        )

        self.run_command(
            f"bash -c 'python3 /sbfl/dump_lines.py {join(self.dir_expr,'src',bug_info[self.key_fix_file])} {lines} > /sbfl/lines.txt'",
            dir_path="/sbfl",
        )

        localize_command = f"python3 ./instrument.py {join(self.dir_expr,'src',bug_info[self.key_bin_path])} /sbfl/lines.txt"

        self.run_command(localize_command, self.log_output_path, dir_path="/sbfl")

        dir_failing_traces = join(self.dir_output, "failing_tests")
        dir_passing_traces = join(self.dir_output, "passing_tests")
        self.run_command("mkdir -p {}".format(dir_failing_traces))
        self.run_command("mkdir -p {}".format(dir_passing_traces))

        self.run_command(
            f"bash -c 'mv /sbfl/*.tracer {join(self.dir_expr,'src',bug_info[self.key_bin_path])}'"
        )

        if not bug_info[self.key_failing_tests] or not bug_info[self.key_passing_tests]:
            self.error_exit("This tool requires positive and negative test cases")

        for failing_test in bug_info[self.key_failing_tests]:
            self.run_command(
                "bash {} {}".format(bug_info[self.key_test_script], failing_test),
                dir_path=self.dir_setup,
                env={"TRACE_FILE": join(dir_failing_traces, failing_test + ".trace")},
            )

        for passing_test in bug_info[self.key_passing_tests]:
            self.run_command(
                "bash {} {}".format(bug_info[self.key_test_script], passing_test),
                dir_path=self.dir_setup,
                env={"TRACE_FILE": join(dir_passing_traces, passing_test + ".trace")},
            )

        status = self.run_command(
            f"python3 /sbfl/sbfl.py {dir_failing_traces} {dir_passing_traces}"
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        output_file = join(self.dir_output, "ochiai.csv")
        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False
        if self.is_file(output_file):
            output_lines = self.read_file(output_file, encoding="iso-8859-1")
            self.stats.fix_loc_stats.plausible = len(output_lines)
            self.stats.fix_loc_stats.generated = len(output_lines)

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
