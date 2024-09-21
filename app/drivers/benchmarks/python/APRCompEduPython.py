import os
from datetime import datetime
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core import abstractions
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class APRCompEduPython(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "aprcomp/benchmark-edupython-2024"
        super(APRCompEduPython, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(APRCompEduPython, self).setup_experiment(
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
        container_id = super(APRCompEduPython, self).setup_container(
            bug_index, image_name, cpu, gpu
        )
        experiment_item = self.experiment_subjects[bug_index - 1]

        root = join(self.dir_expr, "src")

        self.run_command(
            container_id,
            "mkdir -p {}".format(join(root, "code")),
        )

        for dir in ["wrong", "reference", "correct"]:
            self.run_command(
                container_id,
                "mkdir -p {}".format(join(root, "code", dir)),
            )

        self.run_command(
            container_id,
            "cp -r {} {}".format(
                join(self.dir_expr, "base", experiment_item[self.key_subject], "ans"),
                root,
            ),
        )

        self.run_command(
            container_id,
            "cp -r {} {}".format(
                join(
                    self.dir_expr, "base", experiment_item[self.key_subject], "correct"
                ),
                join(root, "code"),
            ),
        )

        self.run_command(
            container_id,
            "cp -r {} {}".format(
                join(self.dir_setup, "reference.py"), join(root, "code", "reference")
            ),
        )

        self.run_command(
            container_id,
            "cp {} {}".format(join(self.dir_setup, "global.py"), join(root, "code")),
        )

        self.run_command(
            container_id,
            "cp -r {} {}".format(
                join(self.dir_setup, experiment_item["source_file"]),
                join(root, "code", "wrong"),
            ),
        )

        self.run_command(
            container_id, "bash -c 'cp -r {}/* {}'".format(self.dir_setup, root)
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
        return True

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
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_verify_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-verify.log"
        )
        time = datetime.now()
        fix_file = experiment_item[self.key_localization][0][self.key_fix_file]
        command_str = f"bash verify_dev {fix_file}"
        status = self.run_command(
            container_id, command_str, self.log_verify_path, self.dir_setup
        )

        self.emit_debug(
            "verify took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

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
        super(APRCompEduPython, self).save_artifacts(dir_info, container_id)
