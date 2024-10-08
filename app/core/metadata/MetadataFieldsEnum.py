from enum import Enum


class MetadataFieldsEnum(Enum):
    ID = "id"
    BUG_ID = "bug_id"
    SUBJECT = "subject"
    SRC = "src"
    LANGUAGE = "language"
    FILE = "file"
    FUNCTION = "function"

    NON_PARSING = "non_parsing"

    SETUP_SCRIPT = "setup_script"
    BUILD_SCRIPT = "build_script"
    BUILD_COMMAND = "build_command"
    CONFIG_SCRIPT = "config_script"
    TEST_SCRIPT = "test_script"
    SCORE = "score"
    ROOT_ABSPATH = "root_abspath"
    ENTRYPOINT = "entrypoint"
    PATCHES_DIR = "patches_dir"

    COUNT_POS = "count_pos"
    COUNT_NEG = "count_neg"
    CRASH_STACK_TRACE = "crash_stack_trace"

    BINARY_PATH = "binary_path"
    BINARY_ARGS = "binary_args"
    TEST_TIMEOUT = "test_timeout"
    ANALYSIS_OUTPUT = "analysis_output"
    BUG_TYPE = "bug_type"
    GENERATOR = "generator"
    CONFIDENCE = "confidence"
    STACK_TRACE = "stack_trace"
    DEPTH = "depth"
    SOURCE_FILE = "source_file"
    LINE = "line"
    LINE_NUMBERS = "line_numbers"
    EXPLOIT_INPUTS = "exploit_inputs"
    BENIGN_INPUTS = "benign_inputs"
    FORMAT = "format"
    DIR = "dir"
    LOCALIZATION = "localization"
    FAILING_TEST_ID = "failing_test_identifiers_id"
    PARSING = "parsing"
    CORRECT = "correct"
    PLAUIBLE_PATCHES_DIR = "plausible_patches_dir"
    ORDERED_PATCHES = "ordered_patches"
    MESSAGE = "message"
    PASSING_TEST_ID = "passing_test_identifiers_id"
    FAILIING = "failing"
    PLAUSIBLE = "plausible"
    FAILING_TEST_IDS = "failing_test_identifiers"
    PASSING_TEST_IDS = "passing_test_identifiers"
    OUTPUT_DIR = "output_dir"
    OUTPUT_DIR_ABSPATH = "output_dir_abspath"
    BENIGN_INPUT_FILES_DIR = "benign_input_files_dir"
    PLAUIBLE_PATCHES = "plausible_patches"
