
class TaskDefaultConfig:

    def __init__(self,
                 compact_results: bool,
                 debug_mode: bool,
                 dump_patches: bool,
                 docker_host: str,
                 only_analyse: bool,
                 only_setup: bool,
                 rebuild_all: bool,
                 rebuild_base: bool,
                 use_cache: bool,
                 use_container: bool,
                 use_gpu: bool,
                 use_purge: bool,
                 max_cpu_count: int
                 ):

        self.compact_results = compact_results
        self.debug_mode = debug_mode
        self.dump_patches = dump_patches
        self.docker_host = docker_host
        self.only_analyse = only_analyse
        self.only_setup = only_setup
        self.rebuild_all = rebuild_all
        self.rebuild_base = rebuild_base
        self.use_cache = use_cache
        self.use_container = use_container
        self.use_gpu = use_gpu
        self.use_purge = use_purge
        self.max_cpu_count = max_cpu_count

    def compact_results(self) -> bool:
        return self.compact_results

    def is_debug_mode(self) -> bool:
        return self.debug_mode

    def dump_patches(self) -> bool:
        return self.dump_patches

    def get_docker_host(self) -> str:
        return self.docker_host

    def only_analyse(self) -> bool:
        return self.only_analyse

    def only_setup(self) -> bool:
        return self.only_setup

    def rebuild_all(self) -> bool:
        return self.rebuild_all

    def rebuild_base(self) -> bool:
        return self.rebuild_base

    def use_container(self) -> bool:
        return self.use_container

    def use_gpu(self) -> bool:
        return self.use_gpu

    def use_purge(self) -> bool:
        return self.use_purge

    def get_max_cpu_count(self) -> int:
        return self.max_cpu_count
