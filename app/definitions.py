import os
from os.path import dirname
DIR_MAIN = dirname(dirname(os.path.realpath(__file__)))
DIR_INFRA = DIR_MAIN + "/infra"
DIRECTORY_LOG_BASE = DIR_MAIN + "/logs"
DIRECTORY_OUTPUT_BASE = DIR_MAIN + "/output"
DIR_EXPERIMENT = DIR_MAIN + "/experiments"
DIR_LOGS = DIRECTORY_OUTPUT_BASE + "/logs"
DIR_RESULT = DIRECTORY_OUTPUT_BASE + "/results"



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
KEY_FIX_LINE = "line_number"
KEY_PASSING_TEST = "passing_test"
KEY_FAILING_TEST = "failing_test"
KEY_CONFIG_TIMEOUT = "timeout"
KEY_CONFIG_TIMEOUT_TESTCASE = "test-timeout"
KEY_CONFIG_FIX_LOC = "fault_location"
KEY_CONFIG_TEST_RATIO = "passing_test_ratio"
KEY_BINARY_PATH = "binary_path"
KEY_COUNT_NEG = "count_neg"
KEY_COUNT_POS = "count_pos"
KEY_CRASH_CMD = "crash_input"


ARG_DATA_PATH = "--data-dir="
ARG_TOOL_PATH = "--tool-path="
ARG_TOOL_NAME = "--tool="
ARG_SUBJECT_NAME = "--subject="
ARG_TOOL_PARAMS = "--tool-param="
ARG_DEBUG_MODE = "--debug"
ARG_ONLY_SETUP = "--only-setup"
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
ARG_INSTRUMENT_ONLY = "--instrument-only"
ARG_RUN_TESTS_ONLY = "--run-tests-only"
ARG_ANALYSE_ONLY = "--analyse-only"
ARG_SHOW_DEV_PATCH = "--show-dev-patch"
ARG_USE_CONTAINER = "--container"


FILE_META_DATA = None
FILE_CONFIGURATION = os.path.dirname(__file__) + "/../configurations/icse22.json"
FILE_OUTPUT_LOG = ""
FILE_SETUP_LOG = ""
FILE_INSTRUMENT_LOG = ""


VOLUME_LIST = {
    DIR_EXPERIMENT: {'bind': '/experiments', 'mode': 'rw'},
    DIR_LOGS: {'bind': '/logs', 'mode': 'rw'},
    DIR_RESULT: {'bind': '/results', 'mode': 'rw'}
}
