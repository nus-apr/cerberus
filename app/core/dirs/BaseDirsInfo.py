import os
from os.path import join


class BaseDirsInfo:

    def __init__(self, dir_main: str):
        self.dir_main = dir_main
        self.dir_app = join(self.dir_main, "app", "")

        # benchmarks dirs
        self.dir_benchmark = join(self.dir_main, "benchmark", "")
        self.dir_benchmark_drivers = join(self.dir_app, "drivers", "benchmarks", "")

        # tools dirs
        self.dir_tool_drivers = join(self.dir_app, "drivers", "tools", "")

        self.dir_libs = join(self.dir_main, "libs")
        self.dir_infra = join(self.dir_main, "infra")
        self.dir_backup = join(self.dir_main, "backup")

        # cerberus logs
        self.dir_log_base = self.init_dir(join(self.dir_main, "logs"))

        # results
        self.dir_results = self.init_dir(join(self.dir_main, "results"))
        self.dir_summaries = self.init_dir(join(self.dir_main, "summaries"))
        self.dir_experiments = self.init_dir(join(self.dir_main, "experiments"))

        # tasks output
        self.dir_output_base = self.init_dir(join(self.dir_main, "output"))
        self.dir_output_logs = self.init_dir(join(self.dir_output_base, "logs"))
        self.dir_output_artifacts = self.init_dir(join(self.dir_output_base, "artifacts"))

    @staticmethod
    def init_dir(dir_path):
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        return dir_path

    def get_main_dir(self):
        return self.dir_main

    def get_app_dir(self):
        return self.dir_app

    def get_benchmark_dir(self):
        return self.dir_benchmark

    def get_log_base_dir(self):
        return self.dir_log_base

    def get_results_dir(self):
        return self.dir_results

    def get_summaries_dir(self):
        return self.dir_summaries

    def get_experiments_dir(self):
        return self.dir_experiments

    def get_output_base_dir(self):
        return self.dir_output_base

    def get_output_log_dir(self):
        return self.dir_output_logs

    def get_output_artifacts_dir(self):
        return self.dir_output_artifacts