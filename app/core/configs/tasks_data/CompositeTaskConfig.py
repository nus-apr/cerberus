from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional
from typing import Tuple
from typing import Union

from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.configs.profiles.ContainerProfile import ContainerProfile
from app.core.configs.profiles.TaskProfile import TaskProfile
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.configs.tasks_data.ToolConfig import ToolConfig
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.TaskType import TaskType


class CompositeTaskConfig(TaskConfig):
    def __init__(
        self,
        composite_sequence: CompositeSequence,
        task_type: TaskType,
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
        use_subject_as_base: bool,
        runs: int = 1,
    ):
        super().__init__(
            task_type,
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
            use_subject_as_base,
            runs,
        )

        self.composite_sequence = composite_sequence
