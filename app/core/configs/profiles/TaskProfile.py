from app.core.configs.profiles.AbstractProfile import AbstractProfile


class TaskProfile(AbstractProfile):
    def __init__(
        self,
        profile_id: str,
        timeout: str,
        fault_location: str,
        passing_test_ratio: float,
        test_timeout: int = 10,
        patch_directory: str = "",
    ):
        super().__init__(profile_id)
        self.timeout = timeout
        self.fault_location = fault_location
        self.passing_test_ratio = passing_test_ratio
        self.test_timeout = test_timeout
        self.patch_directory = patch_directory
