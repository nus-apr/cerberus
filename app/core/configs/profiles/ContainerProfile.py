from app.core.configs.profiles.AbstractProfile import AbstractProfile


class ContainerProfile(AbstractProfile):
    def __init__(
        self,
        profile_id: str,
        cpu_count: int,
        mem_limit: str,
        enable_network: bool,
        gpu_count: int,
    ):
        super().__init__(profile_id)
        self.cpu_count = cpu_count
        self.mem_limit = mem_limit
        self.enable_network = enable_network
        self.gpu_count = gpu_count
