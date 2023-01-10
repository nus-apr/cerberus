import os
from os.path import dirname

DIR_MAIN = dirname(dirname(os.path.realpath(__file__)))
DIR_INFRA = DIR_MAIN + "/infra"
DIR_APP = DIR_MAIN + "/app/"
DIR_TOOL_DRIVERS = DIR_MAIN + "/tools/"
DIR_BENCHMARK_DRIVERS = DIR_MAIN + "/benchmarks/"
DIR_BENCHMARK = DIR_MAIN + "/benchmark/"
DIRECTORY_LOG_BASE = DIR_MAIN + "/logs"
DIRECTORY_OUTPUT_BASE = DIR_MAIN + "/output"
DIR_RESULT = DIR_MAIN + "/results"
DIR_EXPERIMENT = DIR_MAIN + "/experiments"
DIR_LOGS = DIRECTORY_OUTPUT_BASE + "/logs"
DIR_LIBS = DIR_MAIN + "/libs"
DIR_SCRIPTS = DIR_MAIN + "/scripts"
DIR_ARTIFACTS = DIRECTORY_OUTPUT_BASE + "/artifacts"


FILE_MAIN_LOG = ""
FILE_ERROR_LOG = DIRECTORY_LOG_BASE + "/log-error"
FILE_LAST_LOG = DIRECTORY_LOG_BASE + "/log-latest"
FILE_MAKE_LOG = DIRECTORY_LOG_BASE + "/log-make"
FILE_COMMAND_LOG = DIRECTORY_LOG_BASE + "/log-command"
FILE_ANALYSIS_LOG = DIRECTORY_LOG_BASE + "/log-analysis"


KEY_BUG_ID = "bug_id"
KEY_BENCHMARK = "benchmark"
KEY_ID = "id"
KEY_SUBJECT = "subject"
KEY_FIX_FILE = "source_file"
KEY_FIX_LINES = "line_numbers"
KEY_FIX_LOC = "fix_loc"
KEY_PASSING_TEST = "passing_test"
KEY_FAILING_TEST = "failing_test"
KEY_CONFIG_TIMEOUT = "timeout"
KEY_TOOL_PARAMS = "params"
KEY_CONFIG_TIMEOUT_TESTCASE = "test_timeout"
KEY_CONFIG_FIX_LOC = "fault_location"
KEY_CONFIG_TEST_RATIO = "passing_test_ratio"
KEY_BINARY_PATH = "binary_path"
KEY_COUNT_NEG = "count_neg"
KEY_COUNT_POS = "count_pos"
KEY_CRASH_CMD = "crash_input"
KEY_EXPLOIT_LIST = "exploit_file_list"
KEY_FUZZREPAIR_CRASH_CMD = "fuzzrepair_crash_input"
KEY_FUZZREPAIR_EXPLOIT_LIST = "fuzzrepair_exploit_file_list"
KEY_BUG_TYPE = "bug_type"


ARG_DATA_PATH = "--data-dir="
ARG_TOOL_PATH = "--tool-path="
ARG_TOOL_NAME = "--tool="
ARG_TOOL_LIST = "--tool-list="
ARG_SUBJECT_NAME = "--subject="
ARG_TOOL_PARAMS = "--tool-param="
ARG_DEBUG_MODE = "--debug"
ARG_BUG_INDEX = "--bug-index="
ARG_BUG_ID = "--bug-id="
ARG_START_INDEX = "--start-index="
ARG_END_INDEX = "--end-index="
ARG_SKIP_LIST = "--skip-list="
ARG_BUG_INDEX_LIST = "--bug-index-list="
ARG_BUG_ID_LIST = "--bug-id-list="
ARG_BENCHMARK = "--benchmark="
ARG_CONFIG_ID_LIST = "--conf="
ARG_PURGE = "--purge"
ARG_VALIDATOR_THREADS = "--vthread"
ARG_SHOW_DEV_PATCH = "--show-dev-patch"
ARG_USE_LOCAL = "--local"
ARG_USE_CONTAINER = "--container"
ARG_DUMP_PATCHES = "--dump"
ARG_VALKYRIE = "--valkyrie"
ARG_SETUP_ONLY = "--setup-only"
ARG_SKIP_SETUP = "--skip-setup"
ARG_INSTRUMENT_ONLY = "--instrument-only"
ARG_RUN_TESTS_ONLY = "--run-tests-only"
ARG_ANALYSE_ONLY = "--analyse-only"
ARG_REBUILD_ALL_IMAGES = "--rebuild-all"
ARG_REBUILD_EXPERIMENT_IMAGE = "--rebuild-exp"


FILE_META_DATA = None
FILE_CONFIGURATION = os.path.dirname(__file__) + "/../profiles/default.json"
FILE_OUTPUT_LOG = ""
FILE_SETUP_LOG = ""
FILE_INSTRUMENT_LOG = ""

APR_MIN_LIMIT = {
    "prophet": 1000,
    "f1x": 100,
    "genprog": 1000,
    "cpr": 5000,
    "fix2fit": 5000,
    "angelix": 100,
    "senx": 100,
    "darjeeling": 100,
}

APR_MAX_LIMIT = {
    "prophet": 1000,
    "f1x": 5000,
    "genprog": 1000,
    "cpr": 5000,
    "fix2fit": 5000,
    "angelix": 100,
    "senx": 100,
    "darjeeling": 100,
}
