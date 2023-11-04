import os
from datetime import datetime

from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class APRCompFuncC(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(APRCompFuncC, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        if not container_id:
            self.error_exit(
                "unimplemented functionality: this benchmark only runs on docker"
            )

        is_error = True
        if self.install_deps(bug_index, container_id):
            is_error = super(APRCompFuncC, self).setup_experiment(
                bug_index, container_id, test_all
            )
        if not is_error:
            if self.verify(bug_index, container_id):
                self.emit_success("verified successfully")
                if self.transform(bug_index, container_id):
                    self.emit_success("transformation successful")
                else:
                    self.emit_error("transformation failed")
                    is_error = True
            else:
                self.emit_error("verification failed")
                is_error = True
        return is_error

    def install_deps(self, bug_index, container_id):
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

    def deploy(self, bug_index, container_id):
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        time = datetime.now()
        command_str = "bash setup_subject"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        self.emit_debug(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def config(self, bug_index, container_id):
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

    def build(self, bug_index, container_id):
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

    def test(self, bug_index, container_id):
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-test.log"
        )
        time = datetime.now()
        failing_test_list = experiment_item[self.key_failing_tests]
        command_str = f"bash run_test {failing_test_list[0]}"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        self.emit_debug(
            " Test took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status != 0

    def verify(self, bug_index, container_id):
        self.emit_normal("verify dev patch and test-oracle")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-verify.log"
        )
        time = datetime.now()
        failing_test_list = experiment_item[self.key_failing_tests]
        command_str = f"bash verify_dev {failing_test_list[0]}"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )

        self.emit_debug(
            "verify took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def transform(self, bug_index, container_id):
        self.emit_normal("transforming source code")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-transform.log"
        )
        time = datetime.now()
        command_str = "echo 'transformation complete'"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        self.emit_debug(
            "transform took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def clean(self, exp_dir_path, container_id):
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(APRCompFuncC, self).save_artifacts(dir_info, container_id)
