import os
from datetime import datetime

from app.core import definitions
from app.core import emitter
from app.core import values
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Examples(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Examples, self).__init__()

    def deploy(self, bug_index, container_id):
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        time = datetime.now()
        command_str = "bash setup.sh"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        self.emit_debug(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def config(self, bug_id, container_id):
        return True

    def build(self, bug_index, container_id):
        self.emit_normal("building experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        time = datetime.now()
        command_str = "bash build.sh"

        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        self.emit_debug(
            "setup took {} second(s)".format((datetime.now() - time).total_seconds())
        )
        return status == 0

    def test(self, bug_id, container_id):
        return True

    def test_all(self, bug_id, container_id):
        return True

    def verify(self, bug_id, container_id):
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\t[framework] removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str, "/dev/null", "/")
        return

    def save_artifacts(self, dir_info, container_id):
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Examples, self).save_artifacts(dir_info, container_id)
