from typing import List
from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.configs.notifiers.NotifiersConfig import NotifiersConfig
from app.core.configs.profiles.ProfilesConfig import ProfilesConfig
from app.core.configs.tasks_data.TasksChunksConfig import TasksChunksConfig


class Config:

    def __init__(self,
                 general: GeneralConfig,
                 profiles: ProfilesConfig,
                 notifiers: NotifiersConfig,
                 tasks_configs_list: List[TasksChunksConfig]
                 ):
        self.general = general
        self.profiles = profiles
        self.notifiers = notifiers
        self.tasks_configs_list = tasks_configs_list

    def get_general(self) -> GeneralConfig:
        return self.general

    def get_profiles(self) -> ProfilesConfig:
        return self.profiles

    def get_notifiers(self) -> NotifiersConfig:
        return self.notifiers

    def get_tasks_configs_list(self) -> List[TasksChunksConfig]:
        return self.tasks_configs_list
