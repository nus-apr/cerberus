import os
from os.path import join
from typing import Dict
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class ManyBugs(AbstractBenchmark):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ManyBugs, self).__init__()

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_deploy_path = (
            self.dir_logs + "/" + self.name + "-" + bug_id + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, self.dir_setup
        )
        return status == 0

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_config_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-config.log"
        )
        command_str = "bash config.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_config_path, self.dir_setup
        )
        return status == 0

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_build_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-build.log"
        )
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_build_path, self.dir_setup
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-test.log"
        )
        command_str = "bash test.sh {} p1".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def test_all(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing(full) experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-test-all.log"
        )
        failing_test_identifiers_cases = experiment_item[
            self.key_failing_test_identifiers
        ].split(",")
        passing_test_identifiers_cases = experiment_item[
            self.key_passing_test_identifiers
        ].split(",")
        passing_test_identifiers_cases = experiment_item[
            self.key_passing_test_identifiers
        ].split(",")
        unexpected_fail_list = []
        unexpected_pass_list = []
        with open(self.log_test_path, "w") as log_file:
            log_file.write("FAILING TEST CASES\n")
            for test_id in failing_test_identifiers_cases:
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
            for test_id in passing_test_identifiers_cases:
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
                self.emit_warning("unexpected failing test cases")
                log_file.write("unexpected failing list: ")
                for test_id in unexpected_fail_list:
                    log_file.write(str(test_id) + " ")
                    self.emit_warning("unexpected failing test cases" + str(test_id))
                log_file.write("\n")
            else:
                self.emit_success("no unexpected failing test cases")
            if unexpected_pass_list:
                log_file.write("unexpected passing list: ")
                self.emit_warning("unexpected passing test cases")
                for test_id in unexpected_pass_list:
                    log_file.write(str(test_id) + " ")
                    self.emit_warning("unexpected passing test cases" + str(test_id))
                log_file.write("\n")
            else:
                self.emit_success("no unexpected passing test cases")
            log_file.close()
        self.emit_highlight("summary of tests written to: " + self.log_test_path)
        return True

    def transform(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("transform test-suite/fix-file")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id])
        self.log_test_path = (
            self.log_dir_path + "/" + self.name + "-" + bug_id + "-transform.log"
        )
        command_str = "bash transform.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            container_id, command_str, self.log_test_path, self.dir_setup
        )
        return status == 0

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = [
            "/diffs"
        ]  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(ManyBugs, self).save_artifacts(dir_info, container_id)
