from typing import Any
from typing import cast
from typing import Dict
from typing import Optional

from textual.message import Message

from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


class JobAllocate(Message):
    """Job allocation message."""

    bubble = True
    namespace = "cerberus"

    def __init__(
        self,
        index: int,
        benchmark: AbstractBenchmark,
        tool: AbstractTool,
        experiment_item: Dict[str, Any],
        task_config_info: Dict[str, Any],
        container_config_info: Dict[str, Any],
        experiment_image_id: Optional[str],
        identifier: str,
        task_type: TaskType,
        run: str,
        tag: str,
        task_config: TaskConfig,
    ) -> None:
        self.index = index
        self.benchmark = benchmark
        self.tool = tool
        self.experiment_item = experiment_item
        self.task_profile = task_config_info
        self.container_profile = container_config_info
        self.experiment_image_id = experiment_image_id
        self.identifier = identifier
        self.task_type = task_type
        self.task_config = task_config
        self.run = run
        self.tag = tag
        super().__init__()


class JobFinish(Message):
    bubble = True
    namespace = "cerberus"

    def __init__(
        self,
        key: str,
        status: TaskStatus,
        row_data: Any,
        directory_info: Dict[str, str],
        results: ToolStats,
        task_type: TaskType,
    ) -> None:
        self.key = key
        self.status = status
        self.row_data = row_data
        self.directory_info = directory_info
        self.results = results
        self.task_type = task_type
        super().__init__()


class JobMount(Message):
    bubble = False
    namespace = "cerberus"

    def __init__(self, key: str) -> None:
        self.key = key
        super().__init__()


class Write(Message):
    """Write message."""

    namespace = "cerberus"

    def __init__(self, text: str, session_identifier: str) -> None:
        self.text = text
        self.session_identifier = session_identifier
        super().__init__()
