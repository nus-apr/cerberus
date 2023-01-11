import os
from drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app import emitter


class Hippodrome(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Hippodrome, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Hippodrome, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def deploy(self, bug_id, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_id, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        return True

    def build(self, bug_id, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        return True

    def test(self, bug_id, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        return True

    def verify(self, bug_id, container_id):
        emitter.normal("\t\t\tverify dev patch and test-oracle")
        return True

    def transform(self, bug_id, container_id):
        emitter.normal("\t\t\ttransform fix-file")
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Hippodrome, self).save_artefacts(dir_info, container_id)
