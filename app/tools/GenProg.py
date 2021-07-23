import os
import shutil

from app.tools import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values


class GenProg(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__).lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        print("\t[INFO] running repair with", self.name)
        self.log_output_path = dir_logs + "/" + self.name.lower() + "-" + bug_id + "-output.log"
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        count_pass = len(passing_test_list)
        count_neg = len(failing_test_list)
        repair_command = "cd {0}; timeout -k 5m {1}h  ".format(dir_expr + "/src", str(timeout))
        repair_command += "genprog --label-repair  "
        if fix_location:
            source_file, line_number = fix_location.split(":")
            with open(dir_expr + "/src/fault-loc", "w") as loc_file:
                loc_file.write(str(line_number))
            repair_command += " --fault-scheme line " \
                              " --fault-file fault-loc "
        repair_command += " --pos-tests {p_size} " \
                          " --neg-tests {n_size} " \
                          " --test-script \"bash /experiments/benchmark/{benchmark}/{subject}/{bug_id}/test.sh\" " \
            .format(bug_id=bug_id, p_size=count_pass, n_size=count_neg,
                    benchmark="ManyBugs", subject=subject_name)
        repair_command += " repair.conf >> {0} 2>&1 ".format(self.log_output_path)
        execute_command(repair_command)
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        self.save_logs(dir_results)
        dir_patches = dir_expr + "/src/repair"
        if os.path.isdir(dir_patches):
            shutil.copy2(dir_patches, dir_results + "/patches")
        return

