from typing import List

from app.core import values
from app.core.configs.Config import Config
from app.core.configs.ConfigFieldsEnum import ConfigFieldsEnum
from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.configs.profiles.ContainerProfile import ContainerProfile
from app.core.configs.profiles.ProfilesConfig import ProfilesConfig
from app.core.configs.profiles.TaskProfile import TaskProfile
from app.core.configs.tasks_data.BenchmarkConfig import BenchmarkConfig
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.configs.tasks_data.TasksChunksConfig import TasksChunksConfig
from app.core.configs.tasks_data.ToolConfig import ToolConfig


class ConfigDataFactory:
    @staticmethod
    def _create_general_config(general_config_dict: dict) -> GeneralConfig:
        return GeneralConfig(
            parallel_mode=general_config_dict[ConfigFieldsEnum.PARALLEL_MODE.value],
            ui_mode=general_config_dict[ConfigFieldsEnum.UI_MODE.value],
            debug_mode=general_config_dict[ConfigFieldsEnum.DEBUG_MODE.value],
            secure_hash=general_config_dict[ConfigFieldsEnum.SECURE_HASH.value],
        )

    @staticmethod
    def _create_profiles_config(profiles_config_dict: dict) -> ProfilesConfig:

        # load container profiles
        container_profiles_list = []
        for container_profile_dict in profiles_config_dict[
            ConfigFieldsEnum.CONTAINER_PROFILES_LIST.value
        ]:
            container_profiles_list.append(
                ContainerProfile(
                    profile_id=container_profile_dict[
                        ConfigFieldsEnum.PROFILE_ID.value
                    ],
                    cpu_count=container_profile_dict[ConfigFieldsEnum.CPU_COUNT.value],
                    mem_limit=container_profile_dict[ConfigFieldsEnum.MEM_LIMIT.value],
                    enable_network=container_profile_dict[
                        ConfigFieldsEnum.ENABLE_NETWORK.value
                    ],
                )
            )

        # load task profiles
        task_profiles_list = []
        for task_profile_dict in profiles_config_dict[
            ConfigFieldsEnum.TASK_PROFILES_LIST.value
        ]:
            task_profiles_list.append(
                TaskProfile(
                    profile_id=task_profile_dict[ConfigFieldsEnum.PROFILE_ID.value],
                    timeout=task_profile_dict[ConfigFieldsEnum.TIMEOUT.value],
                    fault_location=task_profile_dict[
                        ConfigFieldsEnum.FAULT_LOCATION.value
                    ],
                    passing_test_ratio=task_profile_dict[
                        ConfigFieldsEnum.PASSING_TEST_RATIO.value
                    ],
                )
            )

        return ProfilesConfig(
            task_profiles_list=task_profiles_list,
            container_profiles_list=container_profiles_list,
        )

    @staticmethod
    def _create_tasks_chunks_config(
        tasks_data_config_dict: dict,
    ) -> List[TasksChunksConfig]:
        task_default_config = tasks_data_config_dict[
            ConfigFieldsEnum.DEFAULT_CONFIG.value
        ]

        tasks_chunks_config_list = []
        for tasks_chunk_config_dict in tasks_data_config_dict[
            ConfigFieldsEnum.TASKS_CHUNKS.value
        ]:

            # overwrite task config if necessary
            tasks_chunk_config_dict = {**task_default_config, **tasks_chunk_config_dict}
            task_config = TaskConfig(
                task_type=tasks_chunk_config_dict[ConfigFieldsEnum.TYPE.value],
                compact_results=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.COMPACT_RESULTS.value, values.compact_results
                ),
                dump_patches=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.DUMP_PATCHES.value, values.dump_patches
                ),
                docker_host=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.DOCKER_HOST.value, values.docker_host
                ),
                only_analyse=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.ONLY_ANALYSE.value, values.only_analyse
                ),
                only_setup=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.ONLY_SETUP.value, values.only_setup
                ),
                only_instrument=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.ONLY_INSTRUMENT.value, values.only_instrument
                ),
                only_test=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.ONLY_TEST.value, values.only_test
                ),
                rebuild_all=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.REBUILD_ALL.value, values.rebuild_all
                ),
                rebuild_base=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.REBUILD_BASE.value, values.rebuild_base
                ),
                use_cache=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.USE_CACHE.value, values.use_cache
                ),
                use_container=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.USE_CONTAINER.value, values.use_container
                ),
                use_gpu=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.USE_GPU.value, values.use_gpu
                ),
                use_purge=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.USE_PURGE.value, values.use_purge
                ),
                max_cpu_count=tasks_chunk_config_dict.get(
                    ConfigFieldsEnum.MAX_CPU_COUNT.value, 1
                ),
                runs=tasks_chunk_config_dict.get(ConfigFieldsEnum.RUNS.value, 1),
            )

            benchmarks_config_list = []
            for benchmark_config_dict in tasks_chunk_config_dict[
                ConfigFieldsEnum.BENCHMARKS.value
            ]:
                benchmarks_config_list.append(
                    BenchmarkConfig(
                        name=benchmark_config_dict[ConfigFieldsEnum.NAME.value],
                        bug_id_list=benchmark_config_dict.get(
                            ConfigFieldsEnum.BUG_ID_LIST.value, []
                        ),
                        bug_id_skip_list=benchmark_config_dict.get(
                            ConfigFieldsEnum.BUG_ID_SKIP_LIST.value, []
                        ),
                        bug_subjects_list=benchmark_config_dict.get(
                            ConfigFieldsEnum.BUG_SUBJECTS_LIST.value, []
                        ),
                    )
                )

            tools_config_list = []
            for tool_config_dict in tasks_chunk_config_dict[
                ConfigFieldsEnum.TOOLS.value
            ]:
                tools_config_list.append(
                    ToolConfig(
                        name=tool_config_dict[ConfigFieldsEnum.NAME.value],
                        params=tool_config_dict[ConfigFieldsEnum.PARAMS.value],
                    )
                )

            tasks_chunks_config_list.append(
                TasksChunksConfig(
                    task_config=task_config,
                    container_profile_id_list=tasks_chunk_config_dict[
                        ConfigFieldsEnum.CONTAINER_PROFILE_ID_LIST.value
                    ],
                    task_profile_id_list=tasks_chunk_config_dict[
                        ConfigFieldsEnum.TASK_PROFILE_ID_LIST.value
                    ],
                    benchmarks_config_list=benchmarks_config_list,
                    tools_config_list=tools_config_list,
                )
            )

        return tasks_chunks_config_list

    @staticmethod
    def create(config_data_dict: dict) -> Config:
        return Config(
            general=ConfigDataFactory._create_general_config(
                config_data_dict[ConfigFieldsEnum.GENERAL.value]
            ),
            profiles=ConfigDataFactory._create_profiles_config(
                config_data_dict[ConfigFieldsEnum.PROFILES.value]
            ),
            tasks_configs_list=ConfigDataFactory._create_tasks_chunks_config(
                config_data_dict[ConfigFieldsEnum.TASKS_DATA.value]
            ),
        )
