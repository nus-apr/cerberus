import abc
import os
import json
import shutil
from app import emitter, utilities


class AbstractBenchmark:
    experiment_subjects = []
    meta_file = None
    bench_dir_path = None
    name = None
    log_deploy_path = None
    log_config_path = None
    log_build_path = None
    log_test_path = None
    size = 0

    def __init__(self):
        self.meta_file = self.bench_dir_path + "/meta-data.json"
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
    def setup(self, bug_index, dir_logs, test_all=False):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, exp_dir_path, bug_id, log_dir_path):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, exp_dir_path, bug_id, log_dir_path):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, exp_dir_path, bug_id, log_dir_path):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, exp_dir_path, bug_id, log_dir_path):
        """Method documentation"""
        return

    @abc.abstractmethod
    def save_artefacts(self, results_dir_path, exp_dir_path):
        """Method documentation"""
        return

    @abc.abstractmethod
    def clean(self, exp_dir_path):
        """Method documentation"""
        return

    def save_logs(self, results_dir):
        if os.path.isfile(self.log_deploy_path):
            shutil.move(self.log_deploy_path, results_dir)
        if os.path.isfile(self.log_config_path):
            shutil.move(self.log_config_path, results_dir)
        if os.path.isfile(self.log_build_path):
            shutil.move(self.log_build_path, results_dir)
        if os.path.isfile(self.log_test_path):
            shutil.move(self.log_test_path, results_dir)


