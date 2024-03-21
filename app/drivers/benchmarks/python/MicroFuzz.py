import os
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class MicroFuzz(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(MicroFuzz, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(MicroFuzz, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(MicroFuzz, self).setup_container(
            bug_index, image_name, cpu, gpu
        )
        root = self.dir_expr

        self.run_command(
            container_id,
            "cp -Rf {} {}".format(join(self.dir_setup, "."), root),
        )

        self.run_command(
            container_id,
            "cp -r {} {}".format(join(self.dir_expr, "base", "contest_utils.py"), root),
        )

        return container_id

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def test_all(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        return True

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("[framework] removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(MicroFuzz, self).save_artifacts(dir_info, container_id)
