import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import execute_command
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class ManyBugs(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(
            os.path.dirname(__file__) + "/../../benchmark/"
        )
        self.setup_dir_path = self.bench_dir_path
        super(ManyBugs, self).__init__()

    def deploy(self, bug_index, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_index, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_config_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-config.log"
        )
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        return status == 0

    def build(self, bug_index, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_build_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-build.log"
        )
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        return status == 0

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-test.log"
        )
        command_str = "bash test.sh {} p1".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def test_all(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting(full) experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-test-all.log"
        )
        failing_test_cases = experiment_item[definitions.KEY_FAILING_TEST].split(",")
        passing_test_cases = experiment_item[definitions.KEY_PASSING_TEST].split(",")
        unexpected_fail_list = []
        unexpected_pass_list = []
        with open(self.log_test_path, "w") as log_file:
            log_file.write("FAILING TEST CASES\n")
            for test_id in failing_test_cases:
                command_str = "bash test.sh {} {}".format(
                    self.base_dir_experiment, test_id
                )
                status = self.run_command(
                    container_id, command_str, self.log_test_path, self.dir_setup
                )
                if status != 0:
                    log_file.write("{}: FAIL\n".format(test_id))
                else:
                    log_file.write("{}: PASS\n".format(test_id))
                    unexpected_pass_list.append(test_id)

            log_file.write("PASSING TEST CASES\n")
            for test_id in passing_test_cases:
                command_str = "bash test.sh {} {}".format(
                    self.base_dir_experiment, test_id
                )
                status = self.run_command(
                    container_id, command_str, self.log_test_path, self.dir_setup
                )
                if status != 0:
                    log_file.write("{}: FAIL\n".format(test_id))
                    unexpected_fail_list.append(test_id)
                else:
                    log_file.write("{}: PASS\n".format(test_id))

            if unexpected_fail_list:
                emitter.warning("\t\t\t\t(warning) unexpected failing test cases")
                log_file.write("unexpected failing list: ")
                for test_id in unexpected_fail_list:
                    log_file.write(str(test_id) + " ")
                    emitter.warning("\t\t\t\t\t" + str(test_id))
                log_file.write("\n")
            else:
                emitter.success("\t\t\t\t(success) no unexpected failing test cases")
            if unexpected_pass_list:
                log_file.write("unexpected passing list: ")
                emitter.warning("\t\t\t\t(warning) unexpected passing test cases")
                for test_id in unexpected_pass_list:
                    log_file.write(str(test_id) + " ")
                    emitter.warning("\t\t\t\t\t" + str(test_id))
                log_file.write("\n")
            else:
                emitter.success("\t\t\t\t(success) no unexpected passing test cases")
            log_file.close()
        emitter.highlight("\t\t\tsummary of tests written to: " + self.log_test_path)
        return True

    def transform(self, bug_index, container_id):
        emitter.normal("\t\t\ttransform test-suite/fix-file")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-transform.log"
        )
        command_str = "bash transform.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        emitter.normal("\t\t(benchmark) saving experiment artifacts")
        self.list_artifact_dirs = [
            "/diffs"
        ]  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(ManyBugs, self).save_artifacts(dir_info, container_id)
