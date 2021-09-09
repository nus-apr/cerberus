import abc
import os
import json
import shutil
from app import emitter, utilities, values, container, definitions


class AbstractBenchmark:
    experiment_subjects = []
    meta_file = None
    bench_dir_path = None
    name = None
    log_dir_path = "None"
    log_deploy_path = "None"
    log_config_path = "None"
    log_build_path = "None"
    log_test_path = "None"
    size = 0

    def __init__(self):
        self.meta_file = self.bench_dir_path + "/" + self.name + "/meta-data.json"
        self.load()

    def get_list(self):
        return self.experiment_subjects

    def load(self):
        emitter.normal("loading experiment meta-data")
        if os.path.isfile(self.meta_file):
            with open(self.meta_file, 'r') as in_file:
                json_data = json.load(in_file)
                if json_data:
                    self.experiment_subjects = json_data
                    self.size = len(json_data)
                else:
                    utilities.error_exit("could not load meta-data from ", self.meta_file)
        else:
            utilities.error_exit("Meta file does not exist")
        return

    @abc.abstractmethod
    def setup(self, tool_name, bug_index, dir_logs, test_all=False):
        self.log_dir_path = dir_logs
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        container_id = None
        if values.CONF_USE_CONTAINER:
            self.setup_dir_path = "/setup"
            dir_setup_local = self.bench_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_setup_container = self.setup_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_exp_local = definitions.DIR_EXPERIMENT + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_log_local = definitions.DIR_LOGS + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_result_local = definitions.DIR_RESULT + "/" + self.name + "/" + subject_name + "/" + bug_id
            volume_list = {
                dir_exp_local: {'bind': '/experiments', 'mode': 'rw'},
                dir_log_local: {'bind': '/logs', 'mode': 'rw'},
                dir_result_local: {'bind': '/results', 'mode': 'rw'},
                dir_setup_local: {'bind': dir_setup_container, 'mode': 'rw'}
            }
            container_id = container.get_container(tool_name, self.name, subject_name, bug_id)
            if container_id:
                container.stop_container(container_id)
                container.remove_container(container_id)
            container_id = container.build_container(tool_name, self.name, subject_name, bug_id, volume_list)

        return container_id

    @abc.abstractmethod
    def config(self, exp_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, exp_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, exp_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, exp_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def save_artefacts(self, results_dir_path, exp_dir_path, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def clean(self, exp_dir_path):
        """Method documentation"""
        return

    def save_logs(self, results_dir, container_id):
        if os.path.isfile(self.log_deploy_path):
            shutil.move(self.log_deploy_path, results_dir)
        if os.path.isfile(self.log_config_path):
            shutil.move(self.log_config_path, results_dir)
        if os.path.isfile(self.log_build_path):
            shutil.move(self.log_build_path, results_dir)
        if os.path.isfile(self.log_test_path):
            shutil.move(self.log_test_path, results_dir)


