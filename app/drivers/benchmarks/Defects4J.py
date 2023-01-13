import os
from os.path import join

from app.core import definitions, values, emitter
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Defects4J(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Defects4J, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Defects4J, self).setup_experiment(
            bug_index, container_id, test_all
        )
        return is_error

    def deploy(self, bug_index, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        command_str = "defects4j checkout -p {} -v {}b -w {}".format(
            experiment_item[definitions.KEY_SUBJECT], bug_id, join(self.dir_expr, "src")
        )
        status = self.run_command(container_id, command_str, self.log_deploy_path)
        self.run_command(
            container_id,
            "defects4j export -p cp.test -o classpath_data",
            self.log_deploy_path,
            join(self.dir_expr, "src"),
        )
        for dependency in self.read_file(
            container_id, join(self.dir_expr, "src", "classpath_data")
        )[0].split(":"):
            if dependency.startswith("/defects4j"):
                source = dependency
                destination = "{}/deps/{}".format(
                    self.dir_expr, dependency.split("/defects4j/framework/projects/")[1]
                )
                self.run_command(
                    container_id,
                    "mkdir -p {}".format(os.path.dirname(destination)),
                    log_file_path=self.log_deploy_path,
                )
                self.run_command(
                    container_id,
                    "cp {} {}".format(source, destination),
                    log_file_path=self.log_deploy_path,
                )

        return status == 0

    def config(self, bug_index, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        return True

    def build(self, bug_index, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        command_str = "defects4j compile"
        status = self.run_command(
            container_id, command_str, self.log_build_path, join(self.dir_expr, "src")
        )
        return status == 0

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        command_str = "defects4j test"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, join(self.dir_expr, "src")
        )
        return status == 0

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Defects4J, self).save_artefacts(dir_info, container_id)
