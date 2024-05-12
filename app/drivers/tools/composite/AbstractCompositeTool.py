import os
import shutil
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core import container
from app.core import definitions
from app.core import utilities
from app.core.task.stats.CompositeToolStats import CompositeToolStats
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractCompositeTool(AbstractTool):
    key_composite_sequence = definitions.KEY_COMPOSITE_SEQUENCE

    stats: CompositeToolStats

    def __init__(self, tool_name: str) -> None:
        self.stats = CompositeToolStats()
        self.tool_type = "composite-tool"
        super().__init__(tool_name)

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_patches = dir_info["patches"]
        if os.path.isdir(base_dir_patches):
            dir_patches = join(base_dir_patches, self.name)
            if os.path.isdir(dir_patches):
                shutil.rmtree(dir_patches)
            os.makedirs(dir_patches)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_patches}"
                )
            else:
                save_command = "cp -rf {} {}".format(self.dir_output, f"{dir_patches}")
                utilities.execute_command(save_command)

        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> CompositeToolStats:
        """
        composite tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """

        # if self.is_dir(self.dir_patch):
        #    self.stats.patch_stats.size = len(self.list_dir(self.dir_patch))

        return self.stats

    def save_trace(self) -> None:
        """
        Currently the composite tools do not track their histories.
        """
        pass

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        return
        # self.warning(
        #    "This method should not be called. Composite workflows should be started throught the invoke_advanced method."
        # )
