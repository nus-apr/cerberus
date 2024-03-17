import abc
import os
from datetime import datetime
from os.path import join
from typing import List

from app.core import definitions
from app.core import utilities
from app.core import values
from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractFuzzTool(AbstractTool):
    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_generator = definitions.KEY_GENERATOR
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES
    stats: FuzzToolStats

    def __init__(self, tool_name: str) -> None:
        self.stats = FuzzToolStats()
        self.tool_type = "fuzz-tool"
        super().__init__(tool_name)

    @abc.abstractmethod
    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> FuzzToolStats:
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
