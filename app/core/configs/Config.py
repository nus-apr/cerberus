from typing import List

from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.configs.profiles.ProfilesConfig import ProfilesConfig
from app.core.configs.tasks_data.TasksChunksConfig import TasksChunksConfig


class Config:
    def __init__(
        self,
        general: GeneralConfig,
        profiles: ProfilesConfig,
        tasks_configs_list: List[TasksChunksConfig],
    ):
        self.general = general
        self.profiles = profiles
        self.tasks_configs_list = tasks_configs_list
