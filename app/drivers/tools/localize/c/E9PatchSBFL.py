import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import definitions
from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class E9PatchSBFL(AbstractLocalizeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/sbfl-e9patch:latest"

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

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]

        if self.key_bin_path not in bug_info:
            self.emit_error("No binary path found")

        self.timestamp_log_start()

        self.emit_normal("Instrumenting binary")

        if self.key_fix_file in bug_info:
            self.run_command(
                f"bash -c 'python3 /sbfl/dump_lines.py {join(self.dir_expr,'src',bug_info[self.key_fix_file])} $(cat  {join(self.dir_expr,'src',bug_info[self.key_fix_file])} | wc -l ) >> /sbfl/lines.txt'",
                log_file_path=self.log_output_path,
                dir_path="/sbfl",
            )
        else:
            self.run_command(
                f"bash -c 'for x in $(find {join(self.dir_expr,'src')} | grep -E \".*\\.(c|cpp|hpp|h)$\"); do python3 /sbfl/dump_lines.py $x $(cat $x | wc -l ) >> /sbfl/lines.txt ; done'",
                dir_path="/sbfl",
            )

        localize_command = f"python3 ./instrument.py {join(self.dir_expr,'src',bug_info[self.key_bin_path])} /sbfl/lines.txt"

        self.run_command(localize_command, self.log_output_path, dir_path="/sbfl")

        dir_failing_traces = join(self.dir_output, self.key_failing_test_identifiers)
        dir_passing_traces = join(self.dir_output, self.key_passing_test_identifiers)
        self.run_command("mkdir -p {}".format(dir_failing_traces))
        self.run_command("mkdir -p {}".format(dir_passing_traces))

        self.run_command(
            f"bash -c 'mv /sbfl/*.tracer {join(self.dir_expr,'src',bug_info[self.key_bin_path])}'"
        )

        if (
            not bug_info[self.key_failing_test_identifiers]
            or not bug_info[self.key_passing_test_identifiers]
        ):
            self.error_exit("This tool requires positive and negative test cases")

        for failing_test_identifiers in bug_info[self.key_failing_test_identifiers]:
            self.run_command(
                "bash {} {}".format(
                    bug_info[self.key_test_script], failing_test_identifiers
                ),
                dir_path=self.dir_setup,
                env={
                    "TRACE_FILE": join(
                        dir_failing_traces, failing_test_identifiers + ".trace"
                    )
                },
            )

        for passing_test_identifiers in bug_info[self.key_passing_test_identifiers]:
            self.run_command(
                "bash {} {}".format(
                    bug_info[self.key_test_script], passing_test_identifiers
                ),
                dir_path=self.dir_setup,
                env={
                    "TRACE_FILE": join(
                        dir_passing_traces, passing_test_identifiers + ".trace"
                    )
                },
            )

        status = self.run_command(
            f"python3 /sbfl/sbfl.py {dir_failing_traces} {dir_passing_traces} -a {task_config_info.get(self.key_fl_formula,'ochiai').lower()} {task_config_info.get(self.key_tool_params, '')}",
            log_file_path=self.log_output_path,
        )

        self.run_command("rm -rf {}".format(dir_failing_traces))
        self.run_command("rm -rf {}".format(dir_passing_traces))

        self.process_status(status)

        self.timestamp_log_end()

        if self.is_file(join(self.dir_output, "ochiai.json")):
            localization_info = self.read_json(join(self.dir_output, "ochiai.json"))

            new_metadata = {
                "generator": "e9patchsbfl",
                "confidence": "1",
                "localization": localization_info,
            }

            self.write_json(
                [{self.key_analysis_output: [new_metadata]}],
                join(self.dir_output, "meta-data.json"),
            )

        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        output_file = join(self.dir_output, "ochiai.json")
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
            output_lines = self.read_json(output_file, encoding="iso-8859-1")
            if output_lines:
                fix_files = set()
                fix_locs = set()
                for _l in output_lines:
                    src_file = _l.get(self.key_fix_file)
                    fix_files.add(src_file)
                    for x in _l.get(self.key_fix_lines, []):
                        loc = f"{src_file}:{x}"
                        fix_locs.add(loc)
                self.stats.fix_loc_stats.fix_locs = len(fix_locs)
                self.stats.fix_loc_stats.source_files = len(fix_files)

        else:
            self.emit_error("no output file found")
            self.stats.error_stats.is_error = True

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
