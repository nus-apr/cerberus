import os
from datetime import datetime
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class APRCompAIJava(AbstractBenchmark):
    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "aprcomp/benchmark-aijava-2024"
        super(APRCompAIJava, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(APRCompAIJava, self).setup_experiment(
            bug_index, container_id, test_all
        )
        if not is_error:
            if self.verify(bug_index, container_id):
                self.emit_success("verified successfully")
            else:
                self.emit_error("verification failed")
                is_error = True

        return is_error

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(APRCompAIJava, self).setup_container(
            bug_index, image_name, cpu, gpu
        )

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
            container_id,
            "mvn compile test-compile",
            dir_path=join(self.dir_expr, "src"),
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        failing_test_identifiers_list = experiment_item[
            self.key_failing_test_identifiers
        ]
        command_str = f"bash {experiment_item[self.key_test_script]} {failing_test_identifiers_list[0].replace('::','#')}"
        time = datetime.now()
        failing_status = self.run_command(
            container_id,
            command_str,
            self.log_test_path,
            os.path.join(self.dir_setup),
        )

        passing_test_identifiers_list = experiment_item[
            self.key_passing_test_identifiers
        ]
        passing_status = 0
        if len(passing_test_identifiers_list) != 0:
            command_str = f"bash {experiment_item[self.key_test_script]} {passing_test_identifiers_list[0].replace('::','#')}"
            passing_status = self.run_command(
                container_id,
                command_str,
                self.log_test_path,
                os.path.join(self.dir_setup),
            )
        else:
            self.emit_warning("No passing test provided")

        self.emit_debug(
            "Test took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return failing_status != 0 and passing_status == 0

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("verify dev patch and test-oracle")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_verify_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-verify.log"
        )
        time = datetime.now()
        command_str = f"bash verify_dev"
        status = self.run_command(
            container_id, command_str, self.log_verify_path, self.dir_setup
        )

        self.emit_debug(
            "verify took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(APRCompAIJava, self).save_artifacts(dir_info, container_id)
