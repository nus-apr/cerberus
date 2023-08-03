import os
from os.path import join

from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class AutoCodePython(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(AutoCodePython, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(AutoCodePython, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def setup_container(self, bug_index, image_name, cpu):
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(AutoCodePython, self).setup_container(
            bug_index, image_name, cpu
        )
        root = join(self.dir_expr, "src")

        self.run_command(
            container_id,
            "cp -r {} {}".format(self.dir_setup, root),
        )

        return container_id

    def deploy(self, bug_index, container_id):
        self.emit_normal("downloading experiment subject")
        return True

    def config(self, bug_index, container_id):
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index, container_id):
        self.emit_normal("building experiment subject")
        return True

    def test(self, bug_index, container_id):
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-test.log"
        )
        status = self.run_command(
            container_id,
            "pytest --color=no",
            self.log_test_path,
            join(self.dir_expr, "src"),
        )
        self.emit_debug("Status is {}".format(status))
        return status != 0

    def verify(self, bug_index, container_id):
        self.emit_normal("verify dev patch and test-oracle")
        return True

    def transform(self, bug_index, container_id):
        self.emit_normal("transform fix-file")
        return True

    def clean(self, exp_dir_path, container_id):
        self.emit_normal("[framework] removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(AutoCodePython, self).save_artifacts(dir_info, container_id)
