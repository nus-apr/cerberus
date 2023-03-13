import os
from os.path import dirname
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Tuple

from app.core.analysis import SpaceAnalysis
from app.core.analysis import TimeAnalysis

tool_name = "Cerberus"
docker_host = "unix:///var/run/docker.sock"

dir_main = dirname(dirname(dirname(os.path.realpath(__file__))))
dir_infra = join(dir_main, "infra")
dir_app = join(dir_main, "app", "")
dir_tool_drivers = join(dir_app, "drivers", "tools", "")
dir_benchmark_drivers = join(dir_app, "drivers", "benchmarks", "")
dir_benchmark = join(dir_main, "benchmark", "")
dir_log_base = join(dir_main, "logs")
dir_output_base = join(dir_main, "output")
dir_results = join(dir_main, "results")
dir_experiments = join(dir_main, "experiments")
dir_logs = join(dir_output_base, "logs")
dir_libs = join(dir_main, "libs")
dir_scripts = join(dir_main, "scripts")
dir_artifacts = join(dir_output_base, "artifacts")
dir_output = ""
dir_summaries = join(dir_main, "summaries")
dir_backup = join(dir_main, "backup")


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
tool_list: List[str] = []
debug = False
start_index = None
end_index = None
only_setup = False
skip_setup = False
bug_index_list: List[int] = []
bug_id_list: List[str] = []
skip_index_list: List[int] = []
benchmark_name = ""
profile_id_list: List[str] = []
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
email_setup = False
use_vthreads = False
rebuild_all = False
rebuild_base = False
ui_active = False

default_valkyrie_patch_limit = 200000
default_stack_size = 600000
default_test_timeout = 5
default_valkyrie_timeout = 1
default_valkyrie_waittime = 0.1
default_disk_space = 5  # 5GB
dump_patches = False
arg_pass = False
iteration_no = -1
analysis_results: Dict[str, Tuple[SpaceAnalysis, TimeAnalysis]] = dict()
current_profile_id = None

email_configuration = {
    "ssl_from_start": True,
    "port": 465,
    "host": "",
    "username": "",
    "password": "",
    "to": "",
}


running_tool = False
list_consumed: List[Any] = []
list_processing: List[Any] = []
list_processed: List[Any] = []
list_valid: List[Any] = []
list_invalid: List[Any] = []
list_error: List[Any] = []


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
        l[:-3].lower()
        for l in filter(
            lambda x: "__" not in x and "abstract" not in x.lower(),
            os.listdir(dir_tool_drivers),
        )
    )


def get_list_benchmarks():
    return list(
        l[:-3].lower()
        for l in filter(
            lambda x: "__" not in x and "abstract" not in x.lower(),
            os.listdir(dir_benchmark_drivers),
        )
    )
