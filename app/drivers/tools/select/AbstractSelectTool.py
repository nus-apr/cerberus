import os
import shutil
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import container
from app.core import definitions
from app.core import utilities
from app.core.task.stats.SelectToolStats import SelectToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractSelectTool(AbstractTool):
    stats: SelectToolStats
    dir_selection: str = ""

    def __init__(self, tool_name: str) -> None:
        self.stats = SelectToolStats()
        self.tool_type = "selection-tool"
        super().__init__(tool_name)

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the selection task
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_selection = dir_info["selection"]
        if os.path.isdir(base_dir_selection):
            dir_selection = join(base_dir_selection, self.name)
            if os.path.isdir(dir_selection):
                shutil.rmtree(dir_selection)
            os.makedirs(dir_selection)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_selection}"
                )
            else:
                save_command = "cp -rf {} {}".format(
                    self.dir_output, f"{dir_selection}"
                )
                utilities.execute_command(save_command)

        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> SelectToolStats:
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
