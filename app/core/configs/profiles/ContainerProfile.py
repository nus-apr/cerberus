from app.core.configs.profiles.AbstractProfile import AbstractProfile


class ContainerProfile(AbstractProfile):

    def __init__(self, profile_id: str, cpu_count: int, mem_limit: str, enable_network: bool):

        super().__init__(profile_id)
        self.cpu_count = cpu_count
        self.mem_limit = mem_limit
        self.enable_network = enable_network

    def get_cpu_count(self) -> int:
        return self.cpu_count

    def get_mem_limit(self) -> str:
        return self.mem_limit

    def enable_network(self) -> bool:
        return self.enable_network
