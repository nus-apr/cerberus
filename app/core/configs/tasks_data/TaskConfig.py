from app.core.configs.profiles.AbstractProfile import AbstractProfile
from app.core.configs.tasks_data.TaskDefaultConfig import TaskDefaultConfig
from app.core.configs.tasks_data.ToolConfig import ToolConfig


class TaskConfig(TaskDefaultConfig):

    def __init__(self,
                 task_type: str,
                 compact_results: bool,
                 debug_mode: bool,
                 dump_patches: bool,
                 docker_host: str,
                 only_analyse: bool,
                 only_setup: bool,
                 rebuild_all: bool,
                 rebuild_base: bool,
                 use_cache: bool,
                 use_container: bool,
                 use_gpu: bool,
                 use_purge: bool,
                 max_cpu_count: int,
                 ):

        super().__init__(
            compact_results,
            debug_mode,
            dump_patches,
            docker_host,
            only_analyse,
            only_setup,
            rebuild_all,
            rebuild_base,
            use_cache,
            use_container,
            use_gpu,
            use_purge,
            max_cpu_count
        )

        self.task_type = task_type
        self.task_profile = None
        self.container_profile = None
        self.bug_id = None
        self.benchmark_name = None
        self.tool_config = None

    def get_task_type(self) -> str:
        return self.task_type

    def get_container_profile(self) -> AbstractProfile:
        return self.container_profile

    def set_container_profile(self, container_profile: AbstractProfile):
        self.container_profile = container_profile

    def get_task_profile(self) -> AbstractProfile:
        return self.container_profile

    def set_task_profile(self, task_profile: AbstractProfile):
        self.task_profile = task_profile

    def get_benchmark_name(self) -> str:
        return self.benchmark_name

    def set_benchmark_name(self, benchmark_name: str):
        self.benchmark_name = benchmark_name

    def get_bug_id(self) -> str:
        return self.bug_id

    def set_bug_id(self, bug_id: str):
        self.bug_id = bug_id

    def get_tool_config(self) -> ToolConfig:
        return self.tool_config

    def set_tool_config(self, tool_config: ToolConfig):
        self.tool_config = tool_config
