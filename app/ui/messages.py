from typing import Any
from typing import Dict
from typing import Optional

from textual.message import Message

from app.core.task.status import TaskStatus
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
        experiment_item,
        config_info: Dict[str, Any],
        experiment_image_id: Optional[str],
        identifier: str,
    ) -> None:
        self.index = index
        self.benchmark = benchmark
        self.tool = tool
        self.experiment_item = experiment_item
        self.config_info = config_info
        self.experiment_image_id = experiment_image_id
        self.identifier = identifier
        super().__init__()


class JobFinish(Message):
    bubble = True
    namespace = "cerberus"

    def __init__(self, key, status: TaskStatus, row_data):
        self.key = key
        self.status = status
        self.row_data = row_data
        super().__init__()


class JobMount(Message):
    bubble = False
    namespace = "cerberus"

    def __init__(self, key):
        self.key = key
        super().__init__()


class Write(Message):
    """Write message."""

    namespace = "cerberus"

    def __init__(self, text, identifier):
        self.text = text
        self.identifier = identifier
        super().__init__()
