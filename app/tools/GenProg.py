import os
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
import mmap


class GenProg(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        count_pass = len(passing_test_list)
        count_neg = len(failing_test_list)
        repair_config_str = "--pos-tests {p_size}\n" \
                            "--neg-tests {n_size}\n" \
                            "--test-script bash {dir_exp}/test.sh\n".format(bug_id=bug_id, p_size=count_pass,
                                                                            n_size=count_neg, dir_exp=dir_expr)
        if fix_location:
            source_file, line_number = fix_location.split(":")
            with open(dir_expr + "/src/fault-loc", "w") as loc_file:
                loc_file.write(str(line_number))
            repair_config_str += "--fault-scheme line\n" \
                                 "--fault-file fault-loc\n"

        repair_conf_path = dir_expr + "/src/repair.conf"
        with open(repair_conf_path, "a") as conf_file:
            conf_file.write(repair_config_str)

        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        repair_command = "cd {0}; timeout -k 5m {1}h  ".format(dir_expr + "/src", str(timeout))
        repair_command += "genprog --label-repair --continue "
        repair_command += " repair.conf >> {0} 2>&1 ".format(self.log_output_path)
        status = execute_command(repair_command)
        if status != 0:
            emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        self.save_logs(dir_results, dir_expr, dir_setup, bug_id)
        dir_patches = dir_expr + "/src/repair"
        if os.path.isdir(dir_patches):
            shutil.copytree(dir_patches, dir_results + "/patches")
        return

    def analyse_output(self, dir_results, dir_expr, dir_setup, bug_id):
        emitter.normal("\t\t\t analysing output of " + self.name)
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        with open(self.log_output_path, "r") as log_file:
            log_lines = log_file.readlines()
            for line in log_lines:
                if "variant " in line:
                    count_enumerations = int(line.split("/")[0].split(" ")[-1])
                elif "possible edits" in line:
                    size_search_space = line.split(": ")[2].split(" ")[0]
                elif "fails to compile" in line:
                    count_non_compilable = count_non_compilable + 1
                elif "Repair Found" in line:
                    count_plausible = count_plausible + 1
        return size_search_space, count_enumerations, count_plausible, count_non_compilable


