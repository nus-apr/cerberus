import os
import shutil
from datetime import datetime

from app.core.utilities import execute_command
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class SAVER(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(SAVER, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(SAVER, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def deploy(self, bug_index, container_id):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successdownloading experiment subject"
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        time = datetime.now()
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success Setup took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def config(self, bug_index, container_id):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successconfiguring experiment subject"
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_config_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-config.log"
        )
        time = datetime.now()
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success Config took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def build(self, bug_index, container_id):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successbuilding experiment subject"
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        time = datetime.now()
        command_str = "bash build.sh {}".format(self.base_dir_experiment)

        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_success Setup took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def test(self, bug_index, container_id):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successtesting experiment subject"
        )
        return True

    def clean(self, exp_dir_path, container_id):
        self.emit_normal(
            "self.emit_successself.emit_successself.emit_successremoving experiment subject"
        )
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        self.emit_normal(
            "self.emit_successself.emit_success[benchmark] saving experiment artifacts"
        )
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(SAVER, self).save_artifacts(dir_info, container_id)
