import abc
import os
import shutil
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import container
from app.core import definitions
from app.core import utilities
from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractLocalizeTool(AbstractTool):
    key_fl_formula = definitions.KEY_FL_FORMULA
    stats: LocalizeToolStats

    def __init__(self, tool_name: str) -> None:
        self.stats = LocalizeToolStats()
        self.tool_type = "localize-tool"
        super().__init__(tool_name)

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_localization = dir_info["localization"]
        if os.path.isdir(base_dir_localization):
            dir_localization = join(base_dir_localization, self.name)
            if os.path.isdir(dir_localization):
                shutil.rmtree(dir_localization)
            os.makedirs(dir_localization)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_localization}"
                )
            else:
                save_command = "cp -rf {} {}".format(
                    self.dir_output, f"{dir_localization}"
                )
                utilities.execute_command(save_command)

        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.fix_loc_stats.plausible
            self.stats.fix_loc_stats.size
            self.stats.fix_loc_stats.enumerations
            self.stats.fix_loc_stats.generated

        """

        return self.stats
