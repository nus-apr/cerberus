import os
from os.path import dirname

tool_name = "Cerberus"

dir_main = dirname(dirname(dirname(os.path.realpath(__file__))))
dir_infra = dir_main + "/infra"
dir_app = dir_main + "/app/"
dir_tool_drivers = dir_app + "/drivers/tools/"
dir_benchmark_drivers = dir_app + "/drivers/benchmarks/"
dir_benchmark = dir_main + "/benchmark/"
dir_log_base = dir_main + "/logs"
dir_output_base = dir_main + "/output"
dir_results = dir_main + "/results"
dir_experiments = dir_main + "/experiments"
dir_logs = dir_output_base + "/logs"
dir_libs = dir_main + "/libs"
dir_scripts = dir_main + "/scripts"
dir_artifacts = dir_output_base + "/artifacts"
dir_output = ""
dir_summaries = dir_main + "/summaries"


file_main_log = ""
file_error_log = dir_log_base + "/log-error"
file_last_log = dir_log_base + "/log-latest"
file_command_log = dir_log_base + "/log-command"
file_build_log = dir_log_base + "/log-build"
file_analysis_log = dir_log_base + "/log-analysis"
file_meta_data = None
file_configuration = dir_main + "/profiles/default.json"
file_output_log = ""
file_setup_log = ""
file_instrument_log = ""


data_path = "/data"
tool_path = ""
tool_params = ""
tool_list = []
debug = False
start_index = None
end_index = None
only_setup = False
skip_setup = False
bug_index_list = None
bug_id_list = None
skip_index_list = None
benchmark_name = None
profile_id_list = None
subject_name = None
is_purge = False
only_analyse = False
only_test = False
only_instrument = False
show_dev_patch = False
use_container = True
dump_patches = False
use_valkyrie = False
use_gpu = False
use_vthreads = False
rebuild_all = False
rebuild_base = False

default_valkyrie_patch_limit = 200000
default_stack_size = 600000
default_test_timeout = 5
default_valkyrie_timeout = 1
default_valkyrie_waittime = 0.1
default_disk_space = 5  # 5GB
dump_patches = False
arg_pass = False
iteration_no = -1
analysis_results = dict()
current_profile_id = None


running_tool = False
list_consumed = []
list_processing = []
list_processed = []
list_valid = []
list_invalid = []
list_error = []


apr_min_limit = {
    "prophet": 1000,
    "f1x": 100,
    "genprog": 1000,
    "cpr": 5000,
    "fix2fit": 5000,
    "angelix": 100,
    "senx": 100,
    "darjeeling": 100,
}

apr_max_limit = {
    "prophet": 1000,
    "f1x": 5000,
    "genprog": 1000,
    "cpr": 5000,
    "fix2fit": 5000,
    "angelix": 100,
    "senx": 100,
    "darjeeling": 100,
}


def get_list_tools():
    return list(
        l.replace(".py", "").lower()
        for l in filter(
            lambda x: "__" not in x and "abstract" not in x.lower(),
            os.listdir(dir_tool_drivers),
        )
    )


def get_list_benchmarks():
    return list(
        l.replace(".py", "").lower()
        for l in filter(
            lambda x: "__" not in x and "abstract" not in x.lower(),
            os.listdir(dir_benchmark_drivers),
        )
    )
