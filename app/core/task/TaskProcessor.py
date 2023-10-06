import copy
import os
from typing import List

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.configs.Config import Config
from app.core.task import task
from app.core.task.typing.TaskList import TaskList
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.MockTool import MockTool


class TaskProcessor:
    @staticmethod
    def expand_interval(interval) -> List[int]:
        start_range, end_range = interval.split("-")
        return list(range(int(start_range), int(end_range) + 1))

    @staticmethod
    def normalize_id_list(id_list_raw, size) -> List[int]:
        # TODO: Add support for "*"
        id_list: List[int] = []
        for element in id_list_raw:
            if "*" == element:
                id_list.extend(range(1, size + 1))
            elif "-" in element:
                id_list.extend(TaskProcessor.expand_interval(element))
            else:
                id_list.append(int(element))

        return id_list

    @staticmethod
    def execute(
        config: Config,
    ) -> TaskList:
        for tasks_chunk_config in config.tasks_configs_list:
            for container_profile_id in tasks_chunk_config.container_profile_id_list:
                container_profile = config.profiles.get_container_profile(
                    container_profile_id
                )
                for task_profile_id in tasks_chunk_config.task_profile_id_list:
                    for tool_config in tasks_chunk_config.tools_config_list:
                        for (
                            benchmark_config
                        ) in tasks_chunk_config.benchmarks_config_list:
                            benchmark_name = benchmark_config.name
                            benchmark_template = configuration.load_benchmark(
                                benchmark_name
                            )
                            task_profile = copy.deepcopy(
                                config.profiles.get_task_profile(task_profile_id)
                            )
                            setattr(
                                task_profile,
                                definitions.KEY_TOOL_PARAMS,
                                tool_config.params,
                            )
                            setattr(
                                task_profile,
                                definitions.KEY_TOOL_TAG,
                                tool_config.tag,
                            )

                            benchmark_subjects = (
                                AbstractBenchmark.load_meta_file_static(
                                    os.path.abspath(values.dir_benchmark),
                                    benchmark_name,
                                )
                            )

                            bug_id_list = TaskProcessor.normalize_id_list(
                                benchmark_config.bug_id_list, len(benchmark_subjects)
                            )
                            bug_id_skip_list = TaskProcessor.normalize_id_list(
                                benchmark_config.bug_id_skip_list,
                                len(benchmark_subjects),
                            )
                            bug_subjects_list = benchmark_config.bug_subjects_list

                            if len(bug_subjects_list) != 0:
                                bug_id_list = []
                                for experiment_subject in benchmark_subjects:
                                    if (
                                        experiment_subject[definitions.KEY_SUBJECT]
                                        in bug_subjects_list
                                    ):
                                        bug_id_list.append(
                                            experiment_subject[definitions.KEY_ID]
                                        )

                            values.only_analyse = (
                                tasks_chunk_config.task_config.only_analyse
                            )
                            values.only_setup = (
                                tasks_chunk_config.task_config.only_setup
                            )
                            values.only_instrument = (
                                tasks_chunk_config.task_config.only_instrument
                            )
                            values.only_test = tasks_chunk_config.task_config.only_test

                            if tasks_chunk_config.task_config.task_type != "prepare":
                                tool_template = configuration.load_tool(
                                    tool_config.name,
                                    tasks_chunk_config.task_config.task_type,
                                )
                                if tool_config.image != "":
                                    if tool_config.tag == "":
                                        emitter.warning(
                                            "[framework] tool configuration had an image but no tag, therefore rebuilding everything"
                                        )
                                        values.rebuild_all = True

                                    tool_template.image_name = tool_config.image
                                if not tasks_chunk_config.task_config.only_analyse:
                                    tool_template.check_tool_exists()
                            else:
                                tool_template = MockTool()

                            # filter skipped bug id
                            for bug_id in bug_id_list:
                                if bug_id in bug_id_skip_list:
                                    continue

                                experiment_item = benchmark_subjects[int(bug_id) - 1]

                                bug_index = experiment_item[definitions.KEY_ID]
                                bug_name = str(experiment_item[definitions.KEY_BUG_ID])
                                subject_name = str(
                                    experiment_item[definitions.KEY_SUBJECT]
                                )
                                dir_info = task.generate_dir_info(
                                    benchmark_name, subject_name, bug_name
                                )
                                values.use_container = (
                                    tasks_chunk_config.task_config.use_container
                                )

                                benchmark = copy.deepcopy(benchmark_template)
                                tool = copy.deepcopy(tool_template)
                                benchmark.update_dir_info(dir_info)

                                yield (
                                    tasks_chunk_config.task_config,
                                    (
                                        benchmark,
                                        tool,
                                        experiment_item,
                                        task_profile.__dict__,
                                        container_profile.__dict__,
                                        str(bug_index),
                                    ),
                                )
