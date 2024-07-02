class TaskDefaultConfig:
    def __init__(
        self,
        compact_results: bool,
        dump_patches: bool,
        docker_host: str,
        only_analyse: bool,
        only_setup: bool,
        only_instrument: bool,
        only_test: bool,
        rebuild_all: bool,
        rebuild_base: bool,
        use_cache: bool,
        use_container: bool,
        use_gpu: bool,
        use_purge: bool,
        use_subject_as_base: bool,
        runs: int = 1,
    ):

        self.compact_results = compact_results
        self.dump_patches = dump_patches
        self.docker_host = docker_host
        self.only_analyse = only_analyse
        self.only_setup = only_setup
        self.only_instrument = only_instrument
        self.only_test = only_test
        self.rebuild_all = rebuild_all
        self.rebuild_base = rebuild_base
        self.use_cache = use_cache
        self.use_container = use_container
        self.use_gpu = use_gpu
        self.use_purge = use_purge
        self.use_subject_as_base = use_subject_as_base
        self.runs = runs
