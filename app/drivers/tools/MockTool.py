import os
from typing import List

from app.core.task.stats.ToolStats import ToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.AbstractTool import AbstractTool


class MockTool(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.stats = ToolStats()
        super().__init__(self.name)
        self.image_name = "busybox:latest"

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> ToolStats:
        return super().analyse_output(dir_info, bug_id, fail_list)
