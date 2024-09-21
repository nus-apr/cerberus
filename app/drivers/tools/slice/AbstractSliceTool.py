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
from app.core.task.stats.SliceToolStats import SliceToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractSliceTool(AbstractTool):
    stats: SliceToolStats
    dir_patch: str
    dir_validation: str

    def __init__(self, tool_name: str) -> None:
        self.stats = SliceToolStats()
        self.tool_type = "slice-tool"
        self.dir_patch = ""
        self.dir_validation = ""
        super().__init__(tool_name)

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_validate = dir_info["slicing"]
        if os.path.isdir(base_dir_validate):
            dir_validation = join(base_dir_validate, self.name)
            self.dir_validation = dir_validation
            if os.path.isdir(dir_validation):
                shutil.rmtree(dir_validation)
            os.makedirs(dir_validation)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_validation}"
                )
            else:
                save_command = "cp -rf {} {}".format(
                    self.dir_output, f"{dir_validation}"
                )
                utilities.execute_command(save_command)
        
        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> SliceToolStats:
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

        if self.is_dir(self.dir_patch):
            self.stats.patch_stats.size = len(self.list_dir(self.dir_patch))

        return self.stats
