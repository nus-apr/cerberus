import shutil
import os
from app.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class ManyBugs(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(os.path.dirname(__file__) + "/../../benchmark/" + self.name)
        super(ManyBugs, self).__init__()

    def setup(self, bug_index, dir_logs, test_all=False):
        experiment_item = self.experiment_subjects[bug_index-1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        directory_name = self.bench_dir_path + "/" + subject_name + "/" + bug_id
        emitter.normal("\t\tpreparing experiment subject")
        if self.deploy(directory_name, bug_id, dir_logs):
            if self.config(directory_name, bug_id, dir_logs):
                if self.build(directory_name, bug_id, dir_logs):
                    if test_all:
                        if self.test_all(directory_name, experiment_item, dir_logs):
                            emitter.success("\t\t\t[status] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[error] testing failed")
                    else:
                        if self.test(directory_name, bug_id, dir_logs):
                            emitter.success("\t\t\t[status] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[error] testing failed")
                else:
                    emitter.error("\t\t\t[error] build failed")
            else:
                emitter.error("\t\t\t[error] config failed")
        else:
            emitter.error("\t\t\t[error] deploy failed")
        return

    def deploy(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tdownloading experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_deploy_path = log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-deploy.log"
        command_str = "cd " + exp_dir_path + "; bash setup.sh"
        command_str += " > {0} 2>&1".format(self.log_deploy_path)
        status = execute_command(command_str)
        return status == 0

    def config(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tconfiguring experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_config_path = log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-config.log"
        command_str = "cd " + exp_dir_path + "; bash config.sh"
        command_str += " > {0} 2>&1".format(self.log_config_path)
        status = execute_command(command_str)
        return status == 0

    def build(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\tbuilding experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_build_path = log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-build.log"
        command_str = "cd " + exp_dir_path + "; bash build.sh"
        command_str += " > {0} 2>&1".format(self.log_build_path)
        status = execute_command(command_str)
        return status == 0

    def test(self, exp_dir_path, bug_id, log_dir_path):
        emitter.normal("\t\t\ttesting experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_test_path = log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-test.log"
        command_str = "cd " + exp_dir_path + "; bash test.sh p1"
        command_str += " > {0} 2>&1".format(self.log_test_path)
        status = execute_command(command_str)
        return status == 0

    def test_all(self, exp_dir_path, experiment_item, log_dir_path):
        emitter.normal("\t\t\ttesting(full) experiment subject")
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        conf_id = str(values.CONFIG_ID)
        self.log_test_path = log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-test-all.log"
        failing_test_cases = experiment_item[definitions.KEY_FAILING_TEST].split(",")
        passing_test_cases = experiment_item[definitions.KEY_PASSING_TEST].split(",")
        unexpected_fail_list = []
        unexpected_pass_list = []
        with open(self.log_test_path, "w") as log_file:
            log_file.write("FAILING TEST CASES\n")
            for test_id in failing_test_cases:
                command_str = "cd " + exp_dir_path + "; bash test.sh {}".format(test_id)
                status = execute_command(command_str)
                if status != 0:
                    log_file.write("{}: FAIL\n".format(test_id))
                else:
                    log_file.write("{}: PASS\n".format(test_id))
                    unexpected_pass_list.append(test_id)

            log_file.write("PASSING TEST CASES\n")
            for test_id in passing_test_cases:
                command_str = "cd " + exp_dir_path + "; bash test.sh {}".format(test_id)
                status = execute_command(command_str)
                if status != 0:
                    log_file.write("{}: FAIL\n".format(test_id))
                    unexpected_fail_list.append(test_id)
                else:
                    log_file.write("{}: PASS\n".format(test_id))

            if unexpected_fail_list:
                emitter.warning("\t\t\t\t[warning] unexpected failing test cases")
                log_file.write("unexpected failing list: ")
                for test_id in unexpected_fail_list:
                    log_file.write(str(test_id) + " ")
                    emitter.warning("\t\t\t\t\t" + str(test_id))
                log_file.write("\n")
            else:
                emitter.success("\t\t\t\t[success] no unexpected failing test cases")
            if unexpected_pass_list:
                log_file.write("unexpected passing list: ")
                emitter.warning("\t\t\t\t[warning] unexpected passing test cases")
                for test_id in unexpected_pass_list:
                    log_file.write(str(test_id) + " ")
                    emitter.warning("\t\t\t\t\t" + str(test_id))
                log_file.write("\n")
            else:
                emitter.success("\t\t\t\t[success] no unexpected passing test cases")
            log_file.close()
        emitter.highlight("\t\t\tsummary of tests written to: " + self.log_test_path)
        return True

    def save_artefacts(self, results_dir_path, exp_dir_path):
        self.save_logs(results_dir_path)
        execute_command("cp -rf " + exp_dir_path + "/diffs " + results_dir_path + "/dev-fix")
        return

    def clean(self, exp_dir_path):
        if os.path.isdir(exp_dir_path):
            rm_command = "rm -rf " + exp_dir_path
            execute_command(rm_command)
        return
