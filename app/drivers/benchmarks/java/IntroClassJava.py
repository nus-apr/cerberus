import os
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class IntroClassJava(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(IntroClassJava, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(IntroClassJava, self).setup_experiment(
            bug_index, container_id, test_all
        )

        self.run_command(container_id, "ls -rf /setup")

        if not is_error:
            if self.instrument(bug_index, container_id):
                self.emit_success("[benchmark] instrumentation successful")
            else:
                self.emit_error("[benchmark] instrumentation failed")
                is_error = True
        return is_error

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(IntroClassJava, self).setup_container(
            bug_index, image_name, cpu, gpu
        )

        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        subject = str(experiment_item[self.key_subject])

        self.run_command(
            container_id, "cp -rf {} {}/src".format(self.dir_setup, self.dir_expr)
        )

        return container_id

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        return True

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        status = self.run_command(
            container_id, "mvn compile -DskipTests", dir_path=join(self.dir_expr, "src")
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        status = self.run_command(
            container_id, "mvn test", dir_path=join(self.dir_expr, "src")
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        return status != 0 if bug_id != "reference" else status == 0

    def instrument(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("instrumenting assertions")
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
        super(IntroClassJava, self).save_artifacts(dir_info, container_id)
