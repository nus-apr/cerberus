import os
from typing import Dict
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Hippodrome(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Hippodrome, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(Hippodrome, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        return True

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        return True

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("verify dev patch and test-oracle")
        return True

    def transform(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("transform fix-file")
        return True

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Hippodrome, self).save_artifacts(dir_info, container_id)
