import copy
import os
from os.path import join, dirname
from typing import List

from app.core.configs.Config import Config
from app.core.dirs.BaseDirsInfo import BaseDirsInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class TaskDataFactory:

    @staticmethod
    def expand_interval(interval):
        start_range, start_range = interval.split("-")
        return list(range(start_range, start_range))

    @staticmethod
    def normalize_id_list(id_list_raw):
        # TODO: Add support for "*"
        id_list = []
        for element in id_list_raw:
            if "-" in element:
                id_list.extend(TaskDataFactory.expand_interval(element))
            else:
                id_list.append(element)

        return id_list

    @staticmethod
    def get_tasks_queue(config, base_dirs: BaseDirsInfo):

        for tasks_chunk_config in config.get_tasks_configs_list():
            task_config = copy.deepcopy(tasks_chunk_config.get_task_config())
            print(task_config.get_task_type())

            for container_profile_id in tasks_chunk_config.get_container_profile_id_list():
                container_profile = config.get_profiles().get_container_profile(container_profile_id)
                task_config.set_container_profile(container_profile)

                for task_profile_id in tasks_chunk_config.get_task_profile_id_list():
                    task_profile = config.get_profiles().get_task_profile(task_profile_id)
                    task_config.set_container_profile(task_profile)

                    for tool_config in tasks_chunk_config.get_tools_config_list():
                        task_config.set_tool_config(tool_config)
                        for benchmark_config in tasks_chunk_config.get_benchmarks_config_list():
                            benchmark_name = benchmark_config.get_name()
                            bug_id_list = TaskDataFactory.normalize_id_list(benchmark_config.get_bug_id_list())
                            bug_id_skip_list = TaskDataFactory.normalize_id_list(benchmark_config.get_bug_id_skip_list())
                            bug_subjects_list = benchmark_config.get_bug_subjects_list()
                            if len(bug_subjects_list) != 0:
                                meta_file_path = join(base_dirs.dir_benchmark, benchmark_name, "meta-data.json")
                                experiments_subjects = AbstractBenchmark.load_meta_file(meta_file_path)
                                bug_id_list = []
                                for experiment_subject in experiments_subjects:
                                    if experiment_subject["subject"] in bug_subjects_list:
                                        bug_id_list.append(experiment_subject["id"])

                            # filter skipped bug id
                            bug_id_list = [bug_id for bug_id in bug_id_list if bug_id not in bug_id_skip_list]

                            # here we will create the task that will contain benchmark + tool + configuration
