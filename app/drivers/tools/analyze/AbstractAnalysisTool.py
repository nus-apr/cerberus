import abc
import os
import re
import shutil
import time
from datetime import datetime
from os.path import join

from app.core import abstractions
from app.core import stats
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.utilities import error_exit
from app.core.utilities import execute_command
from app.drivers.tools.AbstractTool import AbstractTool

class AbstractAnalysisTool(AbstractTool):

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

    def run_analysis(self, bug_info, config_info):
        emitter.normal("\t\t(analysis-tool) analysing experiment subject")
        utilities.check_space()
        self.pre_process()
        emitter.normal("\t\t\t running analysis with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return


 def print_stats(
        self, space_info: stats.SpaceStats, time_info: stats.TimeStats
    ):
        emitter.highlight(
            "\t\t\t time duration: {0} seconds".format(time_info.get_duration())
        )