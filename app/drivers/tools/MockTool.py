import os
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.ToolStats import ToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.AbstractTool import AbstractTool


class MockTool(AbstractTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.stats = ToolStats()
        self.tool_type = "mock-tool"
        self.image_name = "busybox:latest"
        super().__init__(self.name)

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> ToolStats:
        return super().analyse_output(dir_info, bug_id, fail_list)
