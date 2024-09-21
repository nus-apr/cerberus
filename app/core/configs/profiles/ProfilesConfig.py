from typing import cast
from typing import Sequence

from app.core.configs.profiles.AbstractProfile import AbstractProfile
from app.core.configs.profiles.ContainerProfile import ContainerProfile
from app.core.configs.profiles.TaskProfile import TaskProfile


class ProfilesConfig:
    def __init__(
        self,
        container_profiles_list: Sequence[ContainerProfile],
        task_profiles_list: Sequence[TaskProfile],
    ):
        self.container_profiles_list = container_profiles_list
        self.task_profiles_list = task_profiles_list

    @staticmethod
    def get_profile_by_id(
        profile_id: str, profiles_list: Sequence[AbstractProfile]
    ) -> AbstractProfile:
        try:
            found_element = next(
                profile for profile in profiles_list if profile.id == profile_id
            )
            return found_element
        except StopIteration:
            err = "Profile with id {0} is not defined.".format(profile_id)
            raise ValueError(err)

    def get_container_profile(self, profile_id: str) -> ContainerProfile:
        return cast(
            ContainerProfile,
            ProfilesConfig.get_profile_by_id(profile_id, self.container_profiles_list),
        )

    def get_task_profile(self, profile_id: str) -> TaskProfile:
        return cast(
            TaskProfile,
            ProfilesConfig.get_profile_by_id(profile_id, self.task_profiles_list),
        )
