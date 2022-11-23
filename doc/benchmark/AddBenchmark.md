# Add New Bug Benchmark
In order to add a new benchmark to the framework, the following requirements should be met

* Benchmark Driver: python class than extends AbstractTool to facilitate standardization of interfaces
* Benchmark Image: a Dockerfile describing how to construct the benchmark container
* Benchmark metadata file: A Json file containing an array of objects with the following features

## Adding a Driver
Create a new file in `app/benchmarks` with the Benchmark name (i.e. NewBenchmark.py) that contains the following code:
```py
import shutil
import os
from os.path import join
from app.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.utilities import execute_command
from app import definitions, values, emitter


class NewBenchmark(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(NewBenchmark, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Defects4J, self).setup_experiment(
            bug_index, container_id, test_all
        )
        experiment_item = self.experiment_subjects[int(bug_index) - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        is_error = status != 0
        if not is_error:
            if self.verify(bug_id, container_id):
                emitter.success("\t\t\t[benchmark] verified successfully")
            else:
                emitter.error("\t\t\t[benchmark] verification failed")
                is_error = True
            if not values.DEFAULT_USE_VALKYRIE:
                emitter.normal("\t\t\tskipping transformation")
            else:
                if self.transform(bug_id, container_id):
                    emitter.success("\t\t\t[benchmark] transformation successful")
                else:
                    emitter.error("\t\t\t[benchmark] transformation failed")
                    is_error = True
        return is_error

    def deploy(self, bug_id, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        return True

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
        super(Defects4J, self).save_artefacts(dir_info, container_id)
```