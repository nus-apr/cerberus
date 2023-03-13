import os

from app.core import emitter
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class ITSP(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ITSP, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(ITSP, self).setup_experiment(bug_index, container_id, test_all)
        return is_error

    def deploy(self, bug_index, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        return True

    def config(self, bug_index, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        return True

    def build(self, bug_index, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        return True

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        return True

    def verify(self, bug_index, container_id):
        emitter.normal("\t\t\tverify dev patch and test-oracle")
        return True

    def transform(self, bug_index, container_id):
        emitter.normal("\t\t\ttransform fix-file")
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        emitter.normal("\t\t(benchmark) saving experiment artifacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(ITSP, self).save_artifacts(dir_info, container_id)
