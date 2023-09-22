import os

from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class ExtractFix(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ExtractFix, self).__init__()

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(ExtractFix, self).setup_experiment(
            bug_index, container_id, test_all
        )

        if not is_error:
            if self.verify(bug_index, container_id):
                self.emit_success("[benchmark] Verified successfully")
            else:
                self.emit_error("[benchmark] Verification failed")
                is_error = True
            if not self.use_valkyrie:
                self.emit_normal("skipping transformation")
            else:
                if self.transform(bug_index, container_id):
                    self.emit_success("[benchmark] Transformation successful")
                else:
                    self.emit_error("[benchmark] Transformation failed")
                    is_error = True
        return is_error

    def deploy(self, bug_index, container_id):
        self.emit_normal("Downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_index, container_id):
        self.emit_normal("configuring experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_config_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-config.log"
        )
        command_str = "bash config.sh"
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        return status == 0

    def build(self, bug_index, container_id):
        self.emit_normal("building experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_build_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-build.log"
        )
        command_str = "bash build.sh"
        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        return status == 0

    def test(self, bug_index, container_id):
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-test.log"
        )
        command_str = "bash test.sh 1"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status != 0

    def verify(self, bug_index, container_id):
        self.emit_normal("verify dev patch and test-oracle")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-verify.log"
        )
        command_str = "bash verify.sh 1"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def transform(self, bug_index, container_id):
        self.emit_normal("transform fix-file")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-transform.log"
        )
        command_str = "bash transform.sh"
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def clean(self, exp_dir_path, container_id):
        self.emit_normal("[framework] removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(ExtractFix, self).save_artifacts(dir_info, container_id)
