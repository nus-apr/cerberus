import abc
from os.path import join

from app.core import definitions
from app.core import utilities
from app.core.task.stats import AnalysisToolStats
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractAnalyzeTool(AbstractTool):
    stats: AnalysisToolStats

    def __init__(self, tool_name):
        self.stats = AnalysisToolStats()
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

    def run_analysis(self, bug_info, repair_config_info):
        self.emit_normal("analysing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.emit_normal("executing analysis command")
        task_conf_id = repair_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")

    def print_stats(self):
        self.emit_highlight(
            "time duration: {0} seconds".format(self.stats.time_stats.get_duration())
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
