import abc
from os.path import join

from app.core import definitions
from app.core import utilities
from app.core.task import stats
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractAnalyzeTool(AbstractTool):
    def __init__(self, tool_name):
        super().__init__(tool_name)

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

    def run_analysis(self, bug_info, repair_config_info):
        self.emit_normal("analysing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.emit_normal("executing analysis command")
        repair_conf_id = repair_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(repair_conf_id, self.name.lower(), bug_id),
        )
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")

    def print_stats(self, space_info: stats.SpaceStats, time_info: stats.TimeStats):
        self.emit_highlight(
            "time duration: {0} seconds".format(time_info.get_duration())
        )

    def emit_normal(self, message):
        super().emit_normal("analyze-tool", self.name, message)

    def emit_warning(self, message):
        super().emit_warning("analyze-tool", self.name, message)

    def emit_error(self, message):
        super().emit_error("analyze-tool", self.name, message)

    def emit_highlight(self, message):
        super().emit_highlight("analyze-tool", self.name, message)

    def emit_success(self, message):
        super().emit_success("analyze-tool", self.name, message)

    def emit_debug(self, message):
        super().emit_debug("analyze-tool", self.name, message)
