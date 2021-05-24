import sys
import json
import subprocess
import os

KEY_BUG_ID = "bug_id"
KEY_BENCHMARK = "benchmark"
KEY_ID = "id"
KEY_SUBJECT = "subject"


ARG_DATA_PATH = "--data-dir="
ARG_TOOL_PATH = "--tool-path="
ARG_TOOL_NAME = "--tool-name="
ARG_TOOL_PARAMS = "--tool-param="
ARG_DEBUG_MODE = "--debug"
ARG_ONLY_SETUP = "--only-setup"
ARG_BUG_ID = "--bug-id="
ARG_START_ID = "--start-id="
ARG_END_ID = "--end-id="
ARG_SKIP_LIST = "--skip-list="
ARG_BUG_ID_LIST = "--bug-id-list="
ARG_BENCHMARK = "--benchmark="


CONF_DATA_PATH = "/data"
CONF_TOOL_PATH = "/CPR"
CONF_TOOL_PARAMS = ""
CONF_TOOL_NAME = None
CONF_DEBUG = False
CONF_BUG_ID = None
CONF_START_ID = None
CONF_END_ID = None
CONF_SETUP_ONLY = False
CONF_BUG_ID_LIST = None
CONF_SKIP_LIST = None
CONF_BENCHMARK = None

FILE_META_DATA = None
FILE_ERROR_LOG = "error-log"

DIR_MAIN = os.getcwd()
DIR_LOGS = DIR_MAIN + "/logs"
DIR_RESULT = DIR_MAIN + "/result"

EXPERIMENT_ITEMS = list()


def create_directories():
    if not os.path.isdir(DIR_LOGS):
        create_command = "mkdir " + DIR_LOGS
        execute_command(create_command)
    if not os.path.isdir(DIR_RESULT):
        create_command = "mkdir " + DIR_RESULT
        execute_command(create_command)


def execute_command(command):
    if CONF_DEBUG:
        print("\t[COMMAND]" + command)
    process = subprocess.Popen([command], stdout=subprocess.PIPE, shell=True)
    (output, error) = process.communicate()
    return int(process.returncode)


def load_experiment_details(meta_file):
    print("[DRIVER] Loading experiment data\n")
    json_data = None
    if os.path.isfile(meta_file):
        with open(FILE_META_DATA, 'r') as in_file:
            json_data = json.load(in_file)
    else:
        exit("Meta file does not exist")
    return json_data


def setup_experiment(script_path, script_name):
    global FILE_ERROR_LOG, CONF_DATA_PATH
    print("\t[INFO] running script for setup")
    script_command = "{ cd " + script_path + "; bash " + script_name + " " + CONF_DATA_PATH + ";}  > /dev/null 2>&1"
    execute_command(script_command)


def cpr(setup_dir_path, deploy_path, bug_id):
    global CONF_TOOL_PARAMS, CONF_TOOL_PATH, CONF_TOOL_NAME, DIR_LOGS
    print("\t[INFO] running CPR")
    conf_path = deploy_path + "/repair.conf"
    script_path = "setup.sh"
    log_path = str(conf_path).replace(".conf", ".log")
    if not os.path.isfile(conf_path):
        setup_dir_path = setup_dir_path + "/cpr"
        setup_command = "cd " + setup_dir_path + "; bash " + script_path + " " + CONF_DATA_PATH + " > /dev/null 2>&1"
        execute_command(setup_command)
    tool_command = "{ " + CONF_TOOL_NAME + " --conf=" + conf_path + " " + CONF_TOOL_PARAMS + ";} 2> " + FILE_ERROR_LOG
    execute_command(tool_command)
    exp_dir = DIR_RESULT + "/" + str(bug_id)
    if os.path.isdir(exp_dir):
        rm_command = "rm -rf " + exp_dir
        execute_command(rm_command)
    mk_command = "mkdir " + exp_dir
    execute_command(mk_command)
    copy_output = "{ cp -rf " + CONF_TOOL_PATH + "/output/" + bug_id + " " + exp_dir + ";} 2> " + FILE_ERROR_LOG
    execute_command(copy_output)
    copy_log = "{ cp " + CONF_TOOL_PATH + "/logs/log-latest " + exp_dir + ";} 2> " + FILE_ERROR_LOG
    execute_command(copy_log)
    copy_log = "cp " + FILE_ERROR_LOG + " " + exp_dir
    execute_command(copy_log)


def angelix(deploy_path, bug_id):
    print("\t[INFO] running Angelix")


def prophet(deploy_path, bug_id):
    print("\t[INFO] running Prophet")


def genprog(deploy_path, bug_id):
    print("\t[INFO] running GenProg")


def fix2fit(deploy_path, bug_id):
    print("\t[INFO] running Fix2Fit")


def repair(deploy_path, setup_dir_path, bug_id):
    global CONF_TOOL_NAME
    if CONF_TOOL_NAME == "cpr":
        cpr(setup_dir_path, deploy_path, bug_id)
    elif CONF_TOOL_NAME == "angelix":
        angelix(deploy_path, bug_id)
    elif CONF_TOOL_NAME == "prophet":
        prophet(deploy_path, bug_id)
    elif CONF_TOOL_NAME == "fix2fit":
        fix2fit(deploy_path, bug_id)
    elif CONF_TOOL_NAME == "genprog":
        genprog(deploy_path, bug_id)
    else:
        exit("Unknown Tool Name")


def print_help():
    print("Usage: python driver.py [OPTIONS] --benchmark={manybugs} --tool-name={cpr/genprog/angelix/prophet/fix2fit} ")
    print("Options are:")
    print("\t" + ARG_DATA_PATH + "\t| " + "directory for experiments")
    print("\t" + ARG_TOOL_NAME + "\t| " + "name of the tool")
    print("\t" + ARG_BENCHMARK + "\t| " + "name of the benchmark")
    print("\t" + ARG_TOOL_PATH + "\t| " + "path of the tool")
    print("\t" + ARG_TOOL_PARAMS + "\t| " + "parameters for the tool")
    print("\t" + ARG_DEBUG_MODE + "\t| " + "enable debug mode")
    print("\t" + ARG_BUG_ID + "\t| " + "run only the specified experiment")
    print("\t" + ARG_BUG_ID_LIST + "\t| " + "runs a list of experiments")
    print("\t" + ARG_START_ID + "\t| " + "specify a range of experiments starting from ID")
    print("\t" + ARG_END_ID + "\t| " + "specify a range of experiments that ends at ID")
    exit()


def read_arg(argument_list):
    global CONF_DATA_PATH, CONF_TOOL_NAME, CONF_TOOL_PARAMS, CONF_START_ID, CONF_END_ID
    global CONF_TOOL_PATH, CONF_DEBUG, CONF_SETUP_ONLY, CONF_BUG_ID, CONF_SKIP_LIST, CONF_BUG_ID_LIST, CONF_BENCHMARK
    global FILE_META_DATA
    print("[DRIVER] Reading configuration values")
    if len(argument_list) > 0:
        for arg in argument_list:
            if ARG_DATA_PATH in arg:
                CONF_DATA_PATH = str(arg).replace(ARG_DATA_PATH, "")
            elif ARG_TOOL_NAME in arg:
                CONF_TOOL_NAME = str(arg).replace(ARG_TOOL_NAME, "").lower()
            elif ARG_TOOL_PATH in arg:
                CONF_TOOL_PATH = str(arg).replace(ARG_TOOL_PATH, "")
            elif ARG_TOOL_PARAMS in arg:
                CONF_TOOL_PARAMS = str(arg).replace(ARG_TOOL_PARAMS, "")
            elif ARG_DEBUG_MODE in arg:
                CONF_DEBUG = True
            elif ARG_ONLY_SETUP in arg:
                CONF_SETUP_ONLY = True
            elif ARG_BUG_ID in arg:
                CONF_BUG_ID = int(str(arg).replace(ARG_BUG_ID, ""))
            elif ARG_START_ID in arg:
                CONF_START_ID = int(str(arg).replace(ARG_START_ID, ""))
            elif ARG_END_ID in arg:
                CONF_END_ID = int(str(arg).replace(ARG_END_ID, ""))
            elif ARG_BENCHMARK in arg:
                CONF_BENCHMARK = str(arg).replace(ARG_BENCHMARK, "")
            elif ARG_SKIP_LIST in arg:
                CONF_SKIP_LIST = str(arg).replace(ARG_SKIP_LIST, "").split(",")
            elif ARG_BUG_ID_LIST in arg:
                CONF_BUG_ID_LIST = str(arg).replace(ARG_BUG_ID_LIST, "").split(",")
            else:
                print("Unknown option: " + str(arg))
                print_help()
    if not CONF_SETUP_ONLY:
        if CONF_TOOL_NAME is None:
            print("[invalid] --tool-name is missing")
            print_help()
    if CONF_START_ID is None and CONF_BUG_ID is None and CONF_BUG_ID_LIST is None:
        print("[info] experiment id is not specified, running all experiments")
    if CONF_BENCHMARK is None:
        print("[invalid] --benchmark is missing")
        print_help()
    else:
        FILE_META_DATA = "benchmark/" + CONF_BENCHMARK + "/meta-data.json"


def run(arg_list):
    global EXPERIMENT_ITEMS, DIR_MAIN, CONF_DATA_PATH, CONF_TOOL_PARAMS, CONF_BUG_ID_LIST
    print("[DRIVER] Running experiment driver")
    read_arg(arg_list)
    EXPERIMENT_ITEMS = load_experiment_details(FILE_META_DATA)
    create_directories()
    index = 1
    for experiment_item in EXPERIMENT_ITEMS:
        if CONF_BUG_ID and index != CONF_BUG_ID:
            index = index + 1
            continue
        if CONF_BUG_ID_LIST and str(index) not in CONF_BUG_ID_LIST:
            index = index + 1
            continue
        if CONF_SKIP_LIST and str(index) in CONF_SKIP_LIST:
            index = index + 1
            continue
        if CONF_START_ID and index < CONF_START_ID:
            index = index + 1
            continue
        if CONF_END_ID and index > CONF_END_ID:
            break

        experiment_name = "Experiment-" + str(index) + "\n-----------------------------"
        print(experiment_name)
        bug_name = str(experiment_item[KEY_BUG_ID])
        subject_name = str(experiment_item[KEY_SUBJECT])
        benchmark = str(experiment_item[KEY_BENCHMARK])
        directory_name = benchmark + "/" + subject_name + "/" + bug_name
        script_name = "setup.sh"

        setup_dir_path = DIR_MAIN + "/benchmark/" + directory_name
        deploy_path = CONF_DATA_PATH + "/" + directory_name + "/"
        print("\t[META-DATA] benchmark: " + benchmark)
        print("\t[META-DATA] project: " + subject_name)
        print("\t[META-DATA] bug ID: " + bug_name)
        print("\t[INFO] setup directory: " + deploy_path)

        if os.path.isdir(deploy_path):
            print("\t[INFO] deployment path exists, skipping setup")
        else:
            setup_experiment(setup_dir_path, script_name)
        if not CONF_SETUP_ONLY:
            repair(deploy_path, setup_dir_path, bug_name)
        index = index + 1


if __name__ == "__main__":
    import sys
    try:
        run(sys.argv[1:])
    except KeyboardInterrupt as e:
        print("[DRIVER] Program Interrupted by User")
        exit()
