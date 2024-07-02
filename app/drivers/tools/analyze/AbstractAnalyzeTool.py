import abc
from os.path import join
from typing import List

from app.core import definitions
from app.core import utilities
from app.core.task.stats.AnalysisToolStats import AnalysisToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractAnalyzeTool(AbstractTool):
    stats: AnalysisToolStats

    def __init__(self, tool_name: str) -> None:
        self.stats = AnalysisToolStats()
        self.tool_type = "analyze-tool"
        super().__init__(tool_name)

    @abc.abstractmethod
    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> AnalysisToolStats:
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
