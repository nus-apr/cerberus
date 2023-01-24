import os
from os.path import join
from datetime import datetime
import shutil
from app.core import definitions, values, emitter, container
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class QuixBugsJava(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(QuixBugsJava, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(QuixBugsJava, self).setup_experiment(
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
        container_id = super(QuixBugsJava, self).setup_container(bug_index, image_name)
        self.run_command(
            container_id, "mkdir {}".format(join(self.dir_expr, "src", ""))
        )
        self.run_command(
            container_id,
            "cp -r {}/java_programs {}".format(
                self.dir_setup, join(self.dir_expr, "src", "")
            ),
        )
        self.run_command(
            container_id,
            "cp -r {}/java_testcases {}".format(
                self.dir_setup, join(self.dir_expr, "src", "")
            ),
        )
        return container_id

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

    def instrument(self, bug_index, container_id):
        emitter.normal("\t\t\tinstrumenting assertions")
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
        super(QuixBugsJava, self).save_artefacts(dir_info, container_id)
