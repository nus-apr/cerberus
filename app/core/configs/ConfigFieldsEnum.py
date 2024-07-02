from enum import Enum


class ConfigFieldsEnum(Enum):
    # general section
    GENERAL = "general"
    UI_MODE = "enable_ui"
    PARALLEL_MODE = "parallel"

    # profiles section
    PROFILES = "profiles"
    TASK_PROFILES_LIST = "task-profiles"
    CONTAINER_PROFILES_LIST = "container-profiles"

    PROFILE_ID = "id"
    TIMEOUT = "timeout"
    FAULT_LOCATION = "fault-location"
    PASSING_TEST_RATIO = "passing-test-ratio"
    PATCH_DIRECTORY = "patch-directory"
    PASSING_TEST_LIMIT = "passing-test-limit"
    FAILING_TEST_LIMIT = "failing-test-limit"

    CPU_COUNT = "cpu-count"
    GPU_COUNT = "gpu-count"
    GPUS = "gpus"
    CPUS = "cpus"
    MEM_LIMIT = "mem-limit"
    ENABLE_NETWORK = "enable-network"

    # notifiers section
    NOTIFIERS = "notifiers"
    ENABLE = "enable"
    EMAIL = "email"
    SLACK = "slack"
    DISCORD = "discord"

    PORT = "port"
    HOST = "host"
    USERNAME = "username"
    PASSWORD = "password"
    RECIPIENTS = "recipients"
    SSL_FROM_START = "ssl-from-start"
    HOOK_URL = "hook-url"
    OAUTH_TOKEN = "oauth-token"
    CHANNEL = "channel"

    # tasks chunks section
    TASKS_DATA = "tasks"
    TASKS_CHUNKS = "chunks"
    DEFAULT_CONFIG = "default"
    RUNS = "runs"

    NAME = "name"
    TYPE = "type"

    REPAIR_TIMEOUT = "repair-timeout"
    FUZZ_TIMEOUT = "fuzz-timeout"
    LOCALIZE_TIMEOUT = "localize-timeout"
    ANALYZE_TIMEOUT = "analyze-timeout"
    COMPOSITE_TIMEOUT = "composite-timeout"
    VALIDATE_TIMEOUT = "validate-timeout"
    SELECT_TIMEOUT = "select-timeout"

    # composite fields
    COMPOSITE_SEQUENCE = "composite-sequence"
    FUZZ = "fuzz"
    VALIDATE = "validate"
    ANALYZE = "analyze"
    CRASH_ANALYZE = "crash-analyze"
    ITERATIVE_REPAIR = "iterative-repair"
    LOCALIZE = "localize"
    SLICE = "slice"
    REPAIR = "repair"
    SELECT = "select"
    ORCHESTRATOR = "orchestrator"

    # benchmarks
    BENCHMARKS = "benchmarks"
    BUG_ID_LIST = "bug-id-list"
    BUG_SUBJECTS_LIST = "bug-subjects-list"
    BUG_ID_SKIP_LIST = "bug-id-skip-list"

    # Tools
    TOOLS = "tools"
    PARAMS = "params"
    TAG = "tag"
    IMAGE = "image"
    HASH_DIGEST = "hash_digest"
    IGNORE = "ignore"
    LOCAL = "local"
    REBUILD = "rebuild"

    # Task Config Params
    COMPACT_RESULTS = "compact-results"
    DEBUG_MODE = "debug-mode"
    DUMP_PATCHES = "dump-patches"
    DOCKER_HOST = "docker-host"
    ONLY_ANALYSE = "only-analyse"
    ONLY_SETUP = "only-setup"
    ONLY_INSTRUMENT = "only-instrument"
    ONLY_TEST = "only-test"
    USE_SUBJECT_AS_BASE = "use-subject-as-base"
    REBUILD_ALL = "rebuild-all"
    REBUILD_BASE = "rebuild-base"
    USE_CACHE = "use-cache"
    USE_CONTAINER = "use-container"
    USE_GPU = "use-gpu"
    USE_PURGE = "use-purge"
    SECURE_HASH = "secure-hash"
    CONTAINER_PROFILE_ID_LIST = "container-profiles-id-list"
    TASK_PROFILE_ID_LIST = "task-profiles-id-list"
