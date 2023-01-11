import os
from drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app import definitions, emitter


class Examples(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(
            os.path.dirname(__file__) + "/../../benchmark/"
        )
        self.setup_dir_path = self.bench_dir_path
        super(Examples, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Examples, self).setup_experiment(
            bug_index, container_id, test_all
        )
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
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
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_id, container_id):
        return True

    def build(self, bug_id, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        return status == 0

    def test(self, bug_id, container_id):
        return True

    def test_all(self, bug_id, container_id):
        return True

    def verify(self, bug_id, container_id):
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(command_str, "/dev/null", "/", container_id)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Examples, self).save_artefacts(dir_info, container_id)
