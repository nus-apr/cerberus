import os

DIR_MAIN = os.path.abspath(os.getcwd() + "/../")
DIR_LOGS = "/logs"
DIR_RESULT = "/results"
DIR_EXPERIMENT = "/experiments"
DIRECTORY_LOG_BASE = DIR_MAIN + "/logs"
FILE_MAIN_LOG = ""
FILE_ERROR_LOG = DIRECTORY_LOG_BASE + "/log-error"
FILE_LAST_LOG = DIRECTORY_LOG_BASE + "/log-latest"
FILE_MAKE_LOG = DIRECTORY_LOG_BASE + "/log-make"
FILE_COMMAND_LOG = DIRECTORY_LOG_BASE + "/log-command"


KEY_BUG_ID = "bug_id"
KEY_BENCHMARK = "benchmark"
KEY_ID = "id"
KEY_SUBJECT = "subject"
KEY_FIX_FILE = "source_file"
KEY_FIX_LINE = "line_number"
KEY_PASSING_TEST = "passing_test"
KEY_FAILING_TEST = "failing_test"
KEY_CONFIG_TIMEOUT = "timeout"
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
ARG_BUG_ID = "--bug-id="
ARG_START_ID = "--start-id="
ARG_END_ID = "--end-id="
ARG_SKIP_LIST = "--skip-list="
ARG_BUG_ID_LIST = "--bug-id-list="
ARG_BENCHMARK = "--benchmark="
ARG_CONFIG_ID_LIST = "--conf="
ARG_PURGE = "--purge"



FILE_META_DATA = None
FILE_CONFIGURATION = os.path.dirname(__file__) + "/../configurations/icse21.json"
FILE_ERROR_LOG = "error-log"
FILE_OUTPUT_LOG = ""
FILE_SETUP_LOG = ""
FILE_INSTRUMENT_LOG = ""