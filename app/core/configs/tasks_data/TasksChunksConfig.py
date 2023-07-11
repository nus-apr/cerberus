from typing import List

from app.core.configs.tasks_data.BenchmarkConfig import BenchmarkConfig
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.configs.tasks_data.ToolConfig import ToolConfig


class TasksChunksConfig:
    def __init__(
        self,
        task_config: TaskConfig,
        container_profile_id_list: List[str],
        task_profile_id_list: List[str],
        benchmarks_config_list: List[BenchmarkConfig],
        tools_config_list: List[ToolConfig],
    ):

        self.task_config = task_config
        self.container_profile_id_list = container_profile_id_list
        self.task_profile_id_list = task_profile_id_list
        self.benchmarks_config_list = benchmarks_config_list
        self.tools_config_list = tools_config_list
