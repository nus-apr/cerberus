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

    CPU_COUNT = "cpu-count"
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

    # Task Config Params
    COMPACT_RESULTS = "compact-results"
    DEBUG_MODE = "debug-mode"
    DUMP_PATCHES = "dump-patches"
    DOCKER_HOST = "docker-host"
    ONLY_ANALYSE = "only-analyse"
    ONLY_SETUP = "only-setup"
    ONLY_INSTRUMENT = "only-instrument"
    ONLY_TEST = "only-test"
    REBUILD_ALL = "rebuild-all"
    REBUILD_BASE = "rebuild-base"
    USE_CACHE = "use-cache"
    USE_CONTAINER = "use-container"
    USE_GPU = "use-gpu"
    USE_PURGE = "use-purge"
    SECURE_HASH = "secure-hash"
    MAX_CPU_COUNT = "max-cpu-count"
    CONTAINER_PROFILE_ID_LIST = "container-profiles-id-list"
    TASK_PROFILE_ID_LIST = "task-profiles-id-list"
