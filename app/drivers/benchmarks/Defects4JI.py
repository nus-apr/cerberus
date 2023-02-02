import os
from os.path import join
from datetime import datetime
import shutil
from app.core import definitions, values, emitter, container
from app.drivers.benchmarks import Defects4J, AbstractBenchmark


class Defects4JI(Defects4J):
    log_instrument_path = None

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Defects4JI, self).setup_experiment(
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
        container_id = super(Defects4JI, self).setup_container(bug_index, image_name)
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])

        bug_name = f"{subject_name.lower()}_{bug_id}"
        instrumented_diff_dir = os.path.join(
            values.dir_benchmark, self.name, "instrumentation", "instrumented-diffs"
        )

        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        diff_file_name = f"{bug_name}.diff"
        if os.path.isdir(instrumented_diff_dir):
            if diff_file_name in os.listdir(instrumented_diff_dir):
                target_path = os.path.join(self.dir_setup, "instrument.diff")
                source_path = os.path.join(instrumented_diff_dir, diff_file_name)
                container.copy_file_to_container(container_id, source_path, target_path)
        return container_id

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
            patch_command = f'bash -c "patch -f -p 1 < {diff_file_path}"'
            status = self.run_command(
                container_id,
                patch_command,
                self.log_instrument_path,
                self.dir_expr + "/src",
            )
            emitter.debug(
                "\t\t\t Instrumentation took {} second(s)".format(
                    (datetime.now() - time).total_seconds()
                )
            )
            if status == 0:
                if not self.build(bug_index, container_id):
                    status = 1
        return status == 0
