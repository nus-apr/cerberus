import os
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class F1X(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):

        print("\t[INFO] running repair with", self.name)
        self.log_output_path = dir_logs+ "/" + self.name.lower() + "-" + bug_id + "-output.log"
        test_driver_path = dir_setup + "/test.sh"
        build_script_path = dir_setup + "/build.sh"
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

        print("\t[INFO] running F1X")
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        repair_command = "cd {0}; timeout -k 5m {1}h f1x ".format(dir_expr, str(timeout))
        repair_command += " -f {0} ".format(abs_path_buggy_file)
        repair_command += " -t {0} ".format(test_id_list)
        repair_command += " -T 15000"
        repair_command += " --driver={0} ".format(test_driver_path)
        repair_command += " -b {0} ".format(build_script_path)
        dry_command = repair_command + " --disable-dteq"
        execute_command(dry_command)
        all_command = repair_command + " --disable-dteq  -a -o patches -v "
        execute_command(all_command)
        repair_command = repair_command + "--enable-validation --disable-dteq  -a -o patches-top --output-top 10 -v"
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
        execute_command(repair_command)

        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        self.save_logs(dir_results)
        dir_patches = dir_expr + "/patches"
        if os.path.isdir(dir_patches):
            shutil.copy2(dir_patches, dir_results + "/patches")
        return
