from typing import Any
from typing import Dict
from typing import Iterable
from typing import Tuple

from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


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
