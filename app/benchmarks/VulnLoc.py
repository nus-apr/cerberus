import shutil
import os
from app.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.utilities import execute_command
from app import definitions, values, emitter


class VulnLoc(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(os.path.dirname(__file__) + "/../../benchmark/")
        self.setup_dir_path = self.bench_dir_path
        super(VulnLoc, self).__init__()


    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(VulnLoc, self).setup_experiment(bug_index, container_id, test_all)
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        if not container_id:
            self.base_dir_experiment = os.path.abspath(os.path.dirname(__file__) + "/../../experiments/")
            dir_exp_local = definitions.DIR_EXPERIMENT + "/" + self.name + "/" + subject_name + "/" + bug_id
            if os.path.isdir(dir_exp_local):
                execute_command("rm -rf {}".format(dir_exp_local))
        if self.verify(bug_id, container_id):
            emitter.success("\t\t\t[benchmark] verified successfully")
        else:
            emitter.error("\t\t\t[benchmark] verification failed")
            is_error = True
        if not values.DEFAULT_USE_VALKYRIE:
            emitter.normal("\t\t\tskipping transformation for vulnfix")
        else:
            if self.transform(bug_id, container_id):
                emitter.success("\t\t\t[benchmark] transformation successful")
            else:
                emitter.error("\t\t\t[benchmark] transformation failed")
                is_error = True
        return is_error

    def deploy(self, bug_id, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        self.log_deploy_path = self.dir_logs + "/" + "-" + self.name + "-" + bug_id + "-deploy.log"
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_deploy_path,
                                  self.dir_setup_container, container_id)
        return status == 0

    def config(self, bug_id, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        self.log_config_path = self.dir_logs + "/" + "-" + self.name + "-" + bug_id + "-config.log"
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_config_path,
                                  self.dir_setup_container, container_id)
        return status == 0

    def build(self, bug_id, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        self.log_build_path = self.dir_logs + "/"  + "-" + self.name + "-" + bug_id + "-build.log"
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_build_path,
                                  self.dir_setup_container, container_id)
        return status == 0

    def test(self, bug_id, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        self.log_test_path = self.dir_logs + "/" + "-" + self.name + "-" + bug_id + "-test.log"
        command_str = "bash test.sh {} 1".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_test_path,
                                  self.dir_setup_container, container_id)
        return status != 0

    def verify(self, bug_id, container_id):
        emitter.normal("\t\t\tverify dev patch and test-oracle")
        self.log_test_path = self.dir_logs + "/" + "-" + self.name + "-" + bug_id + "-verify.log"
        command_str = "bash verify.sh {} 1".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_test_path,
                                  self.dir_setup_container, container_id)
        return status == 0

    def transform(self, bug_id, container_id):
        emitter.normal("\t\t\ttransform fix-file")
        self.log_test_path = self.dir_logs + "/" + "-" + self.name + "-" + bug_id + "-transform.log"
        command_str = "bash transform.sh {}".format(self.base_dir_experiment)
        status = self.run_command(command_str, self.log_test_path,
                                  self.dir_setup_container, container_id)
        return status == 0

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(command_str, "/dev/null", "/", container_id)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = [] # path should be relative to experiment directory
        super(VulnLoc, self).save_artefacts(dir_info, container_id)
