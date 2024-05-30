import os
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class BugJS(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(BugJS, self).__init__()

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(BugJS, self).setup_container(
            bug_index, image_name, cpu, gpu
        )
        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        return container_id

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        subject_id = str(experiment_item[self.key_bug_id]).split("-")[-1]
        command_str = f"bash setup_subject {subject_id}"
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
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-test.log"
        )
        subject_id = str(experiment_item[self.key_bug_id]).split("-")[-1]
        command_str = f"bash test_subject {subject_id}"
        status = self.run_command(
            container_id,
            command_str,
            self.log_test_path,
            os.path.join(self.dir_setup),
        )
        return status == 0

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
        super(BugJS, self).save_artifacts(dir_info, container_id)
