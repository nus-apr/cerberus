import os
import shutil
from datetime import datetime

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import execute_command
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Pulse(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Pulse, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Pulse, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def deploy(self, bug_index, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        time = datetime.now()
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        emitter.normal(
            "\t\t\t Setup took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def config(self, bug_index, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_config_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-config.log"
        )
        time = datetime.now()
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        emitter.normal(
            "\t\t\t Config took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def build(self, bug_index, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        time = datetime.now()
        command_str = "bash build.sh {}".format(self.base_dir_experiment)

        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        emitter.normal(
            "\t\t\t Setup took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return status == 0

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artifacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Pulse, self).save_artifacts(dir_info, container_id)
