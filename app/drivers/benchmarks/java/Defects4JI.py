import os
from datetime import datetime
from os.path import join
from typing import List
from typing import Optional

from app.core import container
from app.drivers.benchmarks.java.Defects4J import Defects4J


class Defects4JI(Defects4J):
    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Defects4JI, self).__init__()

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        is_error = super(Defects4JI, self).setup_experiment(
            bug_index, container_id, test_all
        )
        if not is_error:
            if container_id and self.instrument(bug_index, container_id):
                self.emit_success("instrumentation successful")
            else:
                self.emit_error("[benchmark] instrumentation failed")
                is_error = True
        return is_error

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(Defects4JI, self).setup_container(
            bug_index, image_name, cpu, gpu
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        subject_name = str(experiment_item[self.key_subject])

        bug_name = f"{subject_name.lower()}_{bug_id}"
        instrumented_diff_dir = os.path.join(
            self.dir_benchmark, self.name, "instrumentation", "instrumented-diffs"
        )

        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        diff_file_name = f"{bug_name}.diff"
        if os.path.isdir(instrumented_diff_dir):
            if diff_file_name in os.listdir(instrumented_diff_dir):
                target_path = os.path.join(self.dir_setup, "instrument.diff")
                source_path = os.path.join(instrumented_diff_dir, diff_file_name)
                if container_id:
                    container.copy_file_to_container(
                        container_id, source_path, target_path
                    )
        return container_id

    def instrument(self, bug_index: int, container_id: str) -> bool:
        self.emit_normal("instrumenting assertions")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
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
            self.emit_debug(
                "instrumentation took {} second(s)".format(
                    (datetime.now() - time).total_seconds()
                )
            )
            if status == 0:
                if not self.build(bug_index, container_id):
                    status = 1
        return status == 0
