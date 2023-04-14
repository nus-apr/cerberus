import abc
import os
from datetime import datetime
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.task import stats
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractRepairTool(AbstractTool):
    def __init__(self, tool_name):
        """add initialization commands to all tools here"""
        emitter.debug("using tool: " + tool_name)

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self._space.non_compilable
            self._space.plausible
            self._space.size
            self._space.enumerations
            self._space.generated

            self._time.total_validation
            self._time.total_build
            self._time.timestamp_compilation
            self._time.timestamp_validation
            self._time.timestamp_plausible
        """
        return self._space, self._time, self._error

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        if not self.is_file(join(self.dir_inst, "instrument.sh")):
            return
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.current_profile_id.get("NA"))
        buggy_file = bug_info.get(definitions.KEY_FIX_FILE, "")
        self.log_instrument_path = join(
            self.dir_logs, "{}-{}-{}-instrument.log".format(conf_id, self.name, bug_id)
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        emitter.debug(
            "\t\t\t Instrumentation took {} second(s)".format(
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

    def run_repair(self, bug_info, config_info):
        emitter.normal("\t\t(repair-tool) repairing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        log_file_name = "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id)
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return

    def print_stats(self, space_info: stats.SpaceStats, time_info: stats.TimeStats):
        emitter.highlight("\t\t\t search space size: {0}".format(space_info.size))
        emitter.highlight(
            "\t\t\t count enumerations: {0}".format(space_info.enumerations)
        )
        emitter.highlight(
            "\t\t\t count plausible patches: {0}".format(space_info.plausible)
        )
        emitter.highlight("\t\t\t count generated: {0}".format(space_info.generated))
        emitter.highlight(
            "\t\t\t count non-compiling patches: {0}".format(space_info.non_compilable)
        )
        emitter.highlight(
            "\t\t\t count implausible patches: {0}".format(space_info.get_implausible())
        )

        emitter.highlight(
            "\t\t\t time duration: {0} seconds".format(time_info.get_duration())
        )
        emitter.highlight(
            "\t\t\t time build: {0} seconds".format(time_info.total_build)
        )
        emitter.highlight(
            "\t\t\t time validation: {0} seconds".format(time_info.total_validation)
        )

        if values.use_valkyrie:
            emitter.highlight(
                "\t\t\t time latency compilation: {0} seconds".format(
                    time_info.get_latency_compilation()
                )
            )
            emitter.highlight(
                "\t\t\t time latency validation: {0} seconds".format(
                    time_info.get_latency_validation()
                )
            )
            emitter.highlight(
                "\t\t\t time latency plausible: {0} seconds".format(
                    time_info.get_latency_plausible()
                )
            )
