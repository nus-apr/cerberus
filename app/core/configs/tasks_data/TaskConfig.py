from typing import Any
from typing import Dict
from typing import Optional

from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.configs.profiles.ContainerProfile import ContainerProfile
from app.core.configs.profiles.TaskProfile import TaskProfile
from app.core.configs.tasks_data.TaskDefaultConfig import TaskDefaultConfig
from app.core.configs.tasks_data.ToolConfig import ToolConfig


class TaskConfig(TaskDefaultConfig):
    def __init__(
        self,
        task_type: str,
        compact_results: bool,
        dump_patches: bool,
        docker_host: str,
        only_analyse: bool,
        only_setup: bool,
        only_instrument: bool,
        only_test: bool,
        rebuild_all: bool,
        rebuild_base: bool,
        use_cache: bool,
        use_container: bool,
        use_gpu: bool,
        use_purge: bool,
        max_cpu_count: int,
        runs: int = 1,
    ):

        super().__init__(
            compact_results,
            dump_patches,
            docker_host,
            only_analyse,
            only_setup,
            only_instrument,
            only_test,
            rebuild_all,
            rebuild_base,
            use_cache,
            use_container,
            use_gpu,
            use_purge,
            max_cpu_count,
            runs,
        )

        self.task_type = task_type
        self.task_profile: Optional[TaskProfile] = None
        self.container_profile: Optional[ContainerProfile] = None
        self.bug_id: Optional[str] = None
        self.benchmark_name: Optional[str] = None
        self.tool_config: Optional[ToolConfig] = None
        self.general_config: Optional[GeneralConfig] = None
        self.experiment_info: Dict[str, Any] = {}
