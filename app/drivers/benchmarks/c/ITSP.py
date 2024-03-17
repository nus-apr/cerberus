import os
from datetime import datetime
from typing import Dict
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class ITSP(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ITSP, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(ITSP, self).setup_experiment(bug_index, container_id, test_all)
        return is_error

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        self.run_command(
            container_id, "cp -rf {} {}/src".format(self.dir_setup, self.dir_expr)
        )
        return True

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        time = datetime.now()
        command_str = "bash build_subject"

        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        self.emit_debug(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-test.log"
        )
        time = datetime.now()
        failing_test_identifiers_list = experiment_item[
            self.key_failing_test_identifiers
        ]
        command_str = f"bash run_test {failing_test_identifiers_list[0]}"
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
            command_str = f"bash run_test {passing_test_identifiers_list[0]}"
            passing_status = self.run_command(
                container_id,
                command_str,
                self.log_test_path,
                os.path.join(self.dir_setup),
            )

        self.emit_debug(
            "Test took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return failing_status != 0 and passing_status == 0

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("verify dev patch and test-oracle")
        return True

    def transform(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("transform fix-file")
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
        super(ITSP, self).save_artifacts(dir_info, container_id)
