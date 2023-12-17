import abc
import os
from datetime import datetime
from os.path import join

from app.core import definitions
from app.core import utilities
from app.core import values
from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractFuzzTool(AbstractTool):
    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES
    stats: FuzzToolStats

    def __init__(self, tool_name):
        self.stats = FuzzToolStats()
        super().__init__(tool_name)

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.fuzzing_stats.executions
            self.stats.fuzzing_stats.time_to_bug
            self.stats.fuzzing_stats.total_branches
            self.stats.fuzzing_stats.total_lines
            self.stats.fuzzing_stats.branch_coverage
            self.stats.fuzzing_stats.line_coverage
        """
        return self.stats

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        if not self.is_file(join(self.dir_inst, "instrument.sh")):
            return
        self.emit_normal("running instrumentation script")
        bug_id = bug_info[definitions.KEY_BUG_ID]
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        buggy_file = bug_info.get(definitions.KEY_FIX_FILE, "")
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(task_conf_id, self.name, bug_id),
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        self.emit_debug(
            "\t\t\t instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of {}; exit code {}".format(
                    self.name, str(status)
                )
            )
        return

    def run_fuzz(self, bug_info, fuzzer_config_info):
        self.emit_normal("\t\t[framework] repairing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        self.emit_normal("executing fuzz command")
        task_conf_id = fuzzer_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        log_file_name = "{}-{}-{}-output.log".format(
            task_conf_id, self.name.lower(), bug_id
        )
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")

    def print_stats(self):
        self.stats.write(self.emit_highlight, "\t")

    def emit_normal(self, message):
        super().emit_normal("fuzz-tool", self.name, message)

    def emit_warning(self, message):
        super().emit_warning("fuzz-tool", self.name, message)

    def emit_error(self, message):
        super().emit_error("fuzz-tool", self.name, message)

    def emit_highlight(self, message):
        super().emit_highlight("fuzz-tool", self.name, message)

    def emit_success(self, message):
        super().emit_success("fuzz-tool", self.name, message)

    def emit_debug(self, message):
        super().emit_debug("fuzz-tool", self.name, message)
