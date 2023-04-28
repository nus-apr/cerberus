import abc
import os
from datetime import datetime
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractRepairTool(AbstractTool):

    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_fix_file = definitions.KEY_FIX_FILE
    key_fix_lines = definitions.KEY_FIX_LINES
    key_fix_loc = definitions.KEY_FIX_LOC
    key_failing_tests = definitions.KEY_FAILING_TEST
    key_passing_tests = definitions.KEY_PASSING_TEST
    key_dir_class = definitions.KEY_CLASS_DIRECTORY
    key_dir_source = definitions.KEY_SOURCE_DIRECTORY
    key_dir_tests = definitions.KEY_TEST_DIRECTORY
    key_dir_test_class = definitions.KEY_TEST_CLASS_DIRECTORY
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES

    def __init__(self, tool_name):
        super().__init__(tool_name)

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        return self.stats

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        if not self.is_file(join(self.dir_inst, "instrument.sh")):
            return
        self.emit_normal("running instrumentation script")
        bug_id = bug_info[definitions.KEY_BUG_ID]
        repair_conf_id = str(values.current_repair_profile_id.get("NA"))
        buggy_file = bug_info.get(definitions.KEY_FIX_FILE, "")
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(repair_conf_id, self.name, bug_id),
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        emitter.debug(
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

    def run_repair(self, bug_info, repair_config_info):
        emitter.normal("\t\t[framework] repairing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        self.emit_normal("executing repair command")
        repair_conf_id = repair_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        log_file_name = "{}-{}-{}-output.log".format(
            repair_conf_id, self.name.lower(), bug_id
        )
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return

    def print_stats(self):
        emitter.highlight(
            "\t\t\t search space size: {0}".format(self.stats.patches_stats.size)
        )
        emitter.highlight(
            "\t\t\t count enumerations: {0}".format(
                self.stats.patches_stats.enumerations
            )
        )
        emitter.highlight(
            "\t\t\t count plausible patches: {0}".format(
                self.stats.patches_stats.plausible
            )
        )
        emitter.highlight(
            "\t\t\t count generated: {0}".format(self.stats.patches_stats.generated)
        )
        emitter.highlight(
            "\t\t\t count non-compiling patches: {0}".format(
                self.stats.patches_stats.non_compilable
            )
        )
        emitter.highlight(
            "\t\t\t count implausible patches: {0}".format(
                self.stats.patches_stats.get_implausible()
            )
        )

        emitter.highlight(
            "\t\t\t time duration: {0} seconds".format(
                self.stats.time_stats.get_duration()
            )
        )
        emitter.highlight(
            "\t\t\t time build: {0} seconds".format(self.stats.time_stats.total_build)
        )
        emitter.highlight(
            "\t\t\t time validation: {0} seconds".format(
                self.stats.time_stats.total_validation
            )
        )

        if values.use_valkyrie:
            emitter.highlight(
                "\t\t\t time latency compilation: {0} seconds".format(
                    self.stats.time_stats.get_latency_compilation()
                )
            )
            emitter.highlight(
                "\t\t\t time latency validation: {0} seconds".format(
                    self.stats.time_stats.get_latency_validation()
                )
            )
            emitter.highlight(
                "\t\t\t time latency plausible: {0} seconds".format(
                    self.stats.time_stats.get_latency_plausible()
                )
            )

    def emit_normal(self, message):
        super().emit_normal("repair-tool", self.name, message)

    def emit_warning(self, message):
        super().emit_warning("repair-tool", self.name, message)

    def emit_error(self, message):
        super().emit_error("repair-tool", self.name, message)

    def emit_highlight(self, message):
        super().emit_highlight("repair-tool", self.name, message)

    def emit_success(self, message):
        super().emit_success("repair-tool", self.name, message)

    def emit_debug(self, message):
        super().emit_debug("repair-tool", self.name, message)
