import abc
import os
import json
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

    def __init__(self):
        self.meta_file = self.bench_dir_path + "/meta-data.json"

    def load(self):
        print("[Benchmark] Loading experiment meta-data")
        if os.path.isfile(self.meta_file):
            with open(self.meta_file, 'r') as in_file:
                json_data = json.load(in_file)
                if json_data:
                    self.experiment_subjects = json_data
                else:
                    utilities.error_exit("could not load meta-data from ", self.meta_file)
        else:
            utilities.error_exit("Meta file does not exist")
        return

    @abc.abstractmethod
    def setup(self, exp_dir_path, bug_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, exp_dir_path, bug_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, exp_dir_path, bug_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, exp_dir_path, bug_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, exp_dir_path, bug_id):
        """Method documentation"""
        return




