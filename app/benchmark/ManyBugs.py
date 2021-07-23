from app.benchmark import AbstractBenchmark
from app.utilities import execute_command, error_exit
from app import definitions, values


class ManyBugs(AbstractBenchmark):
    def __init__(self):
        self.name = "ManyBugs"
        self.bench_dir_path = "../../benchmark/" + self.name

    def setup(self, bug_index):
        experiment_item = self.experiment_subjects[bug_index-1]
        bug_id = str([definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        directory_name = self.bench_dir_path + "/" + subject_name + "/" + bug_id
        print("\t[Benchmark] setting up experiment subject")
        if self.deploy(directory_name, bug_id):
            if self.config(directory_name, bug_id):
                if self.build(directory_name, bug_id):
                    if self.test(directory_name, bug_id):
                        print("\t[Benchmark] setting up completed successfully")
                    else:
                        error_exit("\t[Benchmark] test failed")
                else:
                    error_exit("\t[Benchmark] build failed")
            else:
                error_exit("\t[Benchmark] config failed")
        else:
            error_exit("\t[Benchmark] deploy failed")
        return

    def deploy(self, exp_dir_path, bug_id):
        self.log_deploy_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-deploy.log"
        command_str = "cd " + exp_dir_path + "; bash setup.sh;"
        command_str += " > {0} 2>&1".format(self.log_deploy_path)
        status = execute_command(command_str)
        return status

    def config(self, exp_dir_path, bug_id):
        self.log_config_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-config.log"
        command_str = "cd " + exp_dir_path + "; bash config.sh;"
        command_str += " > {0} 2>&1".format(self.log_config_path)
        status = execute_command(command_str)
        return status

    def build(self, exp_dir_path, bug_id):
        self.log_build_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-build.log"
        command_str = "cd " + exp_dir_path + "; bash build.sh;"
        command_str += " > {0} 2>&1".format(self.log_build_path)
        status = execute_command(command_str)
        return status

    def test(self, exp_dir_path, bug_id):
        self.log_test_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-test.log"
        command_str = "cd " + exp_dir_path + "; bash test.sh p1;"
        command_str += " > {0} 2>&1".format(self.log_test_path)
        status = execute_command(command_str)
        return status

    def test_all(self, exp_dir_path, bug_id):
        self.log_test_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-test.log"
        command_str = "cd " + exp_dir_path + "; bash test.sh;"
        command_str += " > {0} 2>&1".format(self.log_test_path)
        status = execute_command(command_str)
        return status
