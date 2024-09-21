import os
from datetime import datetime
from os.path import join
from typing import Dict
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class APRCompFuncJava(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "aprcomp/benchmark-funcjava-2024"
        super(APRCompFuncJava, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        if not container_id:
            self.error_exit(
                "unimplemented functionality: this benchmark only runs on docker"
            )

        is_error = True
        if self.install_deps(bug_index, container_id):
            is_error = super(APRCompFuncJava, self).setup_experiment(
                bug_index, container_id, test_all
            )
        if not is_error:
            if self.compress_dependencies(container_id, bug_index):
                self.emit_success("dependencies compressed successfully")
                if self.verify(bug_index, container_id):
                    self.emit_success("verified successfully")
                    if self.transform(bug_index, container_id):
                        self.emit_success("transformation successful")
                        if self.clean_subject(bug_index, container_id):
                            self.emit_success("clean up successful")
                        else:
                            self.emit_error("clean up failed")
                            is_error = True
                    else:
                        self.emit_error("transformation failed")
                        is_error = True
                else:
                    self.emit_error("verification failed")
                    is_error = True
            else:
                self.emit_error("dependency compression failed")
                is_error = True

        return is_error

    def install_deps(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("installing experiment dependencies")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deps_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deps.log"
        )
        time = datetime.now()
        command_str = "bash install_deps"
        status = self.run_command(
            container_id, command_str, self.log_deps_path, self.dir_setup
        )
        self.emit_debug(
            "installing dependencies took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        time = datetime.now()
        command_str = f"bash setup_subject {experiment_item[self.key_commit_fix]}"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        self.emit_debug(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_config_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-config.log"
        )
        time = datetime.now()
        command_str = "bash config_subject"
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        self.emit_debug(
            "config took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

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

    def compress_dependencies(
        self, container_id: Optional[str], bug_index: int
    ) -> bool:
        self.emit_normal("compressing experiment dependencies")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_compress_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-compress.log"
        )
        time = datetime.now()
        dir_classes = join(self.dir_expr, "src", experiment_item[self.key_dir_class])
        dir_target = "/".join(dir_classes.split("/")[:-1])
        command_str = f"bash compress_deps {dir_target}"
        status = self.run_command(
            container_id, command_str, self.log_compress_path, self.dir_setup
        )
        self.emit_debug(
            " compression took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
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
        test_timeout = experiment_item[self.key_test_timeout]
        command_str = f"bash run_test {failing_test_identifiers_list[0]} {test_timeout}"
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
        if passing_test_identifiers_list:
            passing_test_identifiers_str = ",".join(passing_test_identifiers_list)
            command_str = f"bash run_test {passing_test_identifiers_str} {300}"
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
        failing_test_identifiers_list = experiment_item[
            self.key_failing_test_identifiers
        ]
        test_timeout = experiment_item[self.key_test_timeout]
        command_str = (
            f"bash verify_dev {failing_test_identifiers_list[0]} {test_timeout}"
        )
        status = self.run_command(
            container_id, command_str, self.log_verify_path, self.dir_setup
        )

        self.emit_debug(
            "verify took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def transform(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("transforming source code")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_transform_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-transform.log"
        )
        time = datetime.now()
        command_str = f"bash transform_subject"
        status = self.run_command(
            container_id, command_str, self.log_transform_path, self.dir_setup
        )
        self.emit_debug(
            "transform took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def clean_subject(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("cleaning up source code")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_clean_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-clean.log"
        )
        time = datetime.now()
        command_str = f"bash clean_subject"
        status = self.run_command(
            container_id, command_str, self.log_clean_path, self.dir_setup
        )
        self.emit_debug(
            "clean up took {} second(s)".format((datetime.now() - time).total_seconds())
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
        super(APRCompFuncJava, self).save_artifacts(dir_info, container_id)
