import shutil
import os
from app.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class ManyBugs(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.dirname(__file__) + "/../../benchmark/" + self.name
        super(ManyBugs, self).__init__()

    def setup(self, bug_index, dir_logs):
        experiment_item = self.experiment_subjects[bug_index-1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        directory_name = self.bench_dir_path + "/" + subject_name + "/" + bug_id
        emitter.normal("\t\tpreparing experiment subject")
        if self.deploy(directory_name, bug_id, dir_logs):
            if self.config(directory_name, bug_id, dir_logs):
                if self.build(directory_name, bug_id, dir_logs):
                    if self.test(directory_name, bug_id, dir_logs):
                        emitter.success("\t\t\t[status] setting up completed successfully")
                    else:
                        error_exit("\t[error] test failed")
                else:
                    error_exit("\t[error] build failed")
            else:
                error_exit("\t[error] config failed")
        else:
            error_exit("\t[error] deploy failed")
        return

    def deploy(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tdownloading experiment subject")
        self.log_deploy_path = log_dir_path + "/" + self.name + "-" + bug_id + "-deploy.log"
        command_str = "cd " + exp_dir_path + "; bash setup.sh"
        command_str += " > {0} 2>&1".format(self.log_deploy_path)
        status = execute_command(command_str)
        return status == 0

    def config(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tconfiguring experiment subject")
        self.log_config_path = log_dir_path + "/" + self.name + "-" + bug_id + "-config.log"
        command_str = "cd " + exp_dir_path + "; bash config.sh"
        command_str += " > {0} 2>&1".format(self.log_config_path)
        status = execute_command(command_str)
        return status == 0

    def build(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tbuilding experiment subject")
        self.log_build_path = log_dir_path + "/" + self.name + "-" + bug_id + "-build.log"
        command_str = "cd " + exp_dir_path + "; bash build.sh"
        command_str += " > {0} 2>&1".format(self.log_build_path)
        status = execute_command(command_str)
        return status == 0

    def test(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\ttesting experiment subject")
        self.log_test_path = log_dir_path + "/" + self.name + "-" + bug_id + "-test.log"
        command_str = "cd " + exp_dir_path + "; bash test.sh p1"
        command_str += " > {0} 2>&1".format(self.log_test_path)
        status = execute_command(command_str)
        return status == 0

    def test_all(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\ttesting(full) experiment subject")
        self.log_test_path = log_dir_path + "/" + self.name + "-" + bug_id + "-test.log"
        command_str = "cd " + exp_dir_path + "; bash test.sh"
        command_str += " > {0} 2>&1".format(self.log_test_path)
        status = execute_command(command_str)
        return status == 0

    def save_artefacts(self, results_dir_path, exp_dir_path):
        self.save_logs(results_dir_path)
        execute_command("cp -rf " + exp_dir_path + "/diffs " + results_dir_path + "/dev-fix")
        return

    def clean(self, exp_dir_path):
        if os.path.isdir(exp_dir_path):
            rm_command = "rm -rf " + exp_dir_path
            execute_command(rm_command)
        return
