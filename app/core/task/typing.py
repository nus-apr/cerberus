from typing import Any
from typing import Dict
from typing import Iterable
from typing import Literal
from typing import Tuple

from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


DirectoryInfo = Dict[Literal["local", "container"], Dict[str, str]]
TaskType = Literal["fuzz", "repair", "analyze", "prepare"]
TaskList = Iterable[
    Tuple[
        TaskConfig,
        Tuple[
            AbstractBenchmark,
            AbstractTool,
            Any,
            Dict[str, Any],
            Dict[str, Any],
            str,
        ],
    ]
]
