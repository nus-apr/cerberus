from app.core.configs.profiles.AbstractProfile import AbstractProfile


class TaskProfile(AbstractProfile):

    def __init__(self, profile_id: str, timeout: str, fault_location: str, passing_test_ratio: float):
        
        super().__init__(profile_id)
        self.timeout = timeout
        self.fault_location = fault_location
        self.passing_test_ratio = passing_test_ratio

    def get_timeout(self) -> str:
        return self.timeout

    def get_fault_location(self) -> str:
        return self.fault_location

    def get_passing_test_ratio(self) -> float:
        return self.passing_test_ratio
