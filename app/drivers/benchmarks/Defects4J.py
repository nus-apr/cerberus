import os
from os.path import join
from datetime import datetime
import shutil
from app.core import definitions, values, emitter, container
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Defects4J(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Defects4J, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Defects4J, self).setup_experiment(
            bug_index, container_id, test_all
        )
        if not is_error:
            if self.instrument(bug_index, container_id):
                emitter.success("\t\t\t[benchmark] instrumentation successful")
            else:
                emitter.error("\t\t\t[benchmark] instrumentation failed")
                is_error = True
        return is_error

    def setup_container(self, bug_index, image_name):
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(Defects4J, self).setup_container(bug_index, image_name)
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])

        bug_name = f"{subject_name.lower()}_{bug_id}"
        instrumented_diff_dir = os.path.join(values.dir_benchmark,
                                             self.name,
                                             "instrumentation",
                                             "instrumented-diffs")

        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        diff_file_name = f"{bug_name}.diff"
        if os.path.isdir(instrumented_diff_dir):
            if diff_file_name in os.listdir(instrumented_diff_dir):
                target_path = os.path.join(self.dir_setup, "instrument.diff")
                source_path = os.path.join(instrumented_diff_dir, diff_file_name)
                container.copy_file_to_container(container_id,
                                                 source_path,
                                                 target_path
                                                 )
        return container_id


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
        custom_env = {"JAVA_TOOL_OPTIONS": "-Dfile.encoding=UTF8"}
        command_str = "defects4j compile"
        status = self.run_command(
            container_id, command_str, self.log_build_path, join(self.dir_expr, "src"), custom_env
        )
        return status == 0

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        command_str = "defects4j test"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, join(self.dir_expr, "src")
        )
        return status == 0

    def instrument(self, bug_index, container_id):
        emitter.normal("\t\t\tinstrumenting assertions")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_instrument_path = (
                self.dir_logs + "/" + self.name + "-" + bug_id + "-instrument.log"
        )
        diff_file_path = os.path.join(self.dir_setup, "instrument.diff")
        status = 0
        if container.is_file(container_id, diff_file_path):
            time = datetime.now()
            patch_command = f"bash -c \"patch -f -p 1 < {diff_file_path}\""
            status = self.run_command(
                container_id, patch_command, self.log_instrument_path, self.dir_expr + "/src"
            )
            emitter.debug(
                "\t\t\t Instrumentation took {} second(s)".format(
                    ( datetime.now() - time).total_seconds()
                )
            )
            if status == 0:
                if self.build(bug_index, container_id):
                    status = 1
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
