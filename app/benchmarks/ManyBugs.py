import shutil
import os
from app.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container


class ManyBugs(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(os.path.dirname(__file__) + "/../../benchmark/")
        self.setup_dir_path = self.bench_dir_path
        super(ManyBugs, self).__init__()

    def setup(self, tool_name, bug_index, test_all=False):
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        self.log_dir_path = definitions.DIR_LOGS + "/" + self.name + "/" + subject_name + "/" + bug_id
        container_id = None
        if values.CONF_USE_CONTAINER:
            container_id = self.setup_container(tool_name, bug_index)
        directory_name = self.setup_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
        self.setup_experiment(directory_name, bug_index, container_id, test_all)
        return container_id

    def deploy(self, exp_dir_path, bug_id, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_deploy_path = self.log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-deploy.log"

        if values.CONF_USE_CONTAINER:
            command_str = "bash setup.sh"
            status, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            with open(self.log_deploy_path, 'w') as log_file:
                if stdout:
                    log_file.writelines(stdout.decode("utf-8"))
                if stderr:
                    log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str = "cd " + exp_dir_path + "; bash setup.sh"
            command_str += " > {0} 2>&1".format(self.log_deploy_path)
            status = execute_command(command_str)
        return status == 0

    def config(self, exp_dir_path, bug_id, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_config_path = self.log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-config.log"
        if values.CONF_USE_CONTAINER:
            command_str = "bash config.sh"
            status, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            with open(self.log_config_path, 'w') as log_file:
                if stdout:
                    log_file.writelines(stdout.decode("utf-8"))
                if stderr:
                    log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str = "cd " + exp_dir_path + "; bash config.sh"
            command_str += " > {0} 2>&1".format(self.log_config_path)
            status = execute_command(command_str)

        return status == 0

    def build(self, exp_dir_path, bug_id, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_build_path = self.log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-build.log"

        if values.CONF_USE_CONTAINER:
            command_str = "bash build.sh"
            status, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            with open(self.log_build_path, 'w') as log_file:
                if stdout:
                    log_file.writelines(stdout.decode("utf-8"))
                if stderr:
                    log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str = "cd " + exp_dir_path + "; bash build.sh"
            command_str += " > {0} 2>&1".format(self.log_build_path)
            status = execute_command(command_str)
        return status == 0

    def test(self, exp_dir_path, bug_id, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        conf_id = str(values.CONFIG_ID)
        self.log_test_path = self.log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-test.log"

        if values.CONF_USE_CONTAINER:
            command_str = "bash test.sh p1"
            status, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            with open(self.log_test_path, 'w') as log_file:
                if stdout:
                    log_file.writelines(stdout.decode("utf-8"))
                if stderr:
                    log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str = "cd " + exp_dir_path + "; bash test.sh p1"
            command_str += " > {0} 2>&1".format(self.log_test_path)
            status = execute_command(command_str)
        return status == 0

    def test_all(self, exp_dir_path, experiment_item, container_id):
        emitter.normal("\t\t\ttesting(full) experiment subject")
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        conf_id = str(values.CONFIG_ID)
        self.log_test_path = self.log_dir_path + "/" + conf_id + "-" + self.name + "-" + bug_id + "-test-all.log"
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

    def save_artefacts(self, results_dir_path, exp_dir_local, container_id, bug_index):
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        exp_dir_path = exp_dir_local
        if values.CONF_USE_CONTAINER:
            exp_dir_path = "/experiment/" + self.name + "/" + subject_name + "/" + bug_id
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.save_logs(results_dir_path)
        self.save_dev_patch(results_dir_path, exp_dir_path, container_id)

    def clean(self, exp_dir_path):
        if os.path.isdir(exp_dir_path):
            rm_command = "rm -rf " + exp_dir_path
            execute_command(rm_command)
        return

    def save_dev_patch(self, results_dir_path, exp_dir_path, container_id=None):
        emitter.normal("\t\t\tsaving experiment dev-patch")
        if container_id:
            execute_command("docker cp "+ container_id + ":" + exp_dir_path + "/diffs/. " + results_dir_path + "/dev-fix")
        else:
            execute_command("cp -rf " + exp_dir_path + "/diffs " + results_dir_path + "/dev-fix")
        return
