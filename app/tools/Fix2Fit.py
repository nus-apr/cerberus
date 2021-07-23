import os
import shutil

from app.tools import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values


class Fix2Fit(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__).lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        print("\t[INFO] running repair with", self.name)
        self.log_output_path = dir_logs+ "/" + self.name.lower() + "-" + bug_id + "-output.log"
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        abs_path_binary = dir_expr + "/src/" + binary_path
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + " "
        if passing_test_list:
            for test_id in passing_test_list:
                test_id_list += test_id + " "

        if fix_location:
            abs_path_buggy_file = dir_expr + "/src/" + fix_location
        else:
            with open(dir_expr + "/manifest.txt", "r") as man_file:
                abs_path_buggy_file = dir_expr + "/src/" + man_file.readlines()[0].strip().replace("\n", "")

        print("\t[INFO] running Fix2Fit")
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        repair_command = "export SUBJECT_DIR={0}; ".format(dir_setup)
        repair_command += "export BUGGY_FILE={0}; ".format(abs_path_buggy_file)
        repair_command += "export TESTCASE=\"{0}\"; ".format(test_id_list)
        repair_command += "export DRIVER=./test.sh; "
        repair_command += "export BINARY={0}; ".format(abs_path_binary)
        repair_command += "export TIME_OUT={0}; ".format(abs_path_binary)
        repair_command += "export BINARY_INPUT=\"{0}\"; ".format(binary_arg)
        repair_command += "cd {0}; timeout -k 5m {1}h bash /src/scripts/run.sh ".format(dir_setup, str(timeout))
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
        execute_command(repair_command)
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        self.save_logs(dir_results)
        dir_patches = dir_setup + "/patches"
        if os.path.isdir(dir_patches):
            shutil.copy2(dir_patches, dir_results + "/patches")
        return

    def save_logs(self, dir_results, dir_setup, bug_id):
        super(Fix2Fit, self).save_logs(dir_results)
        patch_gen_log = dir_setup + "/original.txt"
        shutil.copy(patch_gen_log, dir_results)
