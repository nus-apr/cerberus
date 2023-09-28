import os
from datetime import datetime
from os.path import join

from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class effFix(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(effFix, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = True
        if self.deps(bug_index, container_id):
            is_error = super(effFix, self).setup_experiment(
                bug_index, container_id, test_all
            )
        return is_error

    def deploy(self, bug_index, container_id):
        self.emit_normal("downloading experiment subject")
        time = datetime.now()
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        self.emit_normal(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def deps(self, bug_index, container_id):
        self.emit_normal("installing experiment dependencies")
        time = datetime.now()
        if self.is_file(f"{self.dir_setup}/deps.sh", container_id):
            command_str = "bash deps.sh {}".format(self.base_dir_experiment)
            status = self.run_command(
                container_id, command_str, self.log_deps_path, self.dir_setup
            )
            self.emit_normal(
                "dependencies took {} second(s)".format(
                    (datetime.now() - time).total_seconds()
                )
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
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        self.emit_normal(
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
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        self.emit_normal(
            "build took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def test(self, bug_index, container_id):
        self.emit_normal("testing experiment subject")
        return True

    def clean(self, exp_dir_path, container_id):
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(effFix, self).save_artifacts(dir_info, container_id)
