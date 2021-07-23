import os
import shutil

from app.tools import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values


class Prophet(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__).lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        print("\t[INFO] running repair with", self.name)
        self.log_output_path = dir_logs+ "/" + self.name.lower() + "-" + bug_id + "-output.log"
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)

        test_config_str = "-\n"
        test_config_str += "-\n"
        test_config_str += "Diff Cases: Tot {0}\n".format(len(failing_test_list))
        for test_id in failing_test_list:
            if test_id == failing_test_list[-1]:
                test_config_str += test_id + "\n"
            else:
                test_config_str += test_id + " "
        test_config_str += "Positive Cases: Tot {0}\n".format(len(passing_test_list))
        for test_id in passing_test_list:
            if test_id == passing_test_list[-1]:
                test_config_str += test_id + "\n"
            else:
                test_config_str += test_id + " "
        test_config_str += "Regression Cases: Tot 0\n"
        test_config_file = dir_expr + "/prophet/prophet.revlog"

        if not os.path.isfile(test_config_file):
            open(test_config_file, "w")
        with open(test_config_file, "r+") as conf_file:
            conf_file.seek(0)
            conf_file.write(test_config_str)
            conf_file.truncate()
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        if not os.path.isdir(dir_expr + "/workdir"):
            instrument_command = "cd " + dir_expr + ";"
            instrument_command += "prophet prophet/prophet.conf  -r workdir -init-only "
            instrument_command += " >> " + self.log_output_path + " 2>&1"
            execute_command(instrument_command)
        line_number = ""
        localization_file = dir_expr + "/workdir/profile_localization.res"
        if fix_location:
            source_file, line_number = fix_location.split(":")
            fault_loc = "{file_path} {line} {column} {file_path} {line} {column}" \
                        " \t\t\t 3000000 \t\t 687352 \t\t 16076\n".format(file_path=source_file, line=line_number,
                                                                          column=3)
            if not os.path.isfile(localization_file):
                open(localization_file, "w")
            with open(localization_file, "r+") as res_file:
                res_file.seek(0)
                res_file.write(fault_loc)
                res_file.truncate()
        else:
            if not os.path.isfile(localization_file) or os.path.getsize(localization_file) == 0:
                if os.path.isfile(dir_setup + "/prophet/profile_localization.res"):
                    shutil.copy(dir_setup + "/prophet/profile_localization.res", localization_file)

        print("\t[INFO] running Prophet")
        repair_command = "timeout -k 5m {0}h prophet -feature-para /prophet-gpl/crawler/para-all.out ".format(timeout)
        repair_command += " -full-synthesis -full-explore "
        repair_command += " -r {0}".format(dir_expr + "/workdir")
        repair_command += " -cond-ext -replace-ext -skip-verify "
        repair_command += " -timeout {0} ".format(int(timeout))
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
        execute_command(repair_command)
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        self.save_logs(dir_results)
        regex_for_fix = "*-fix-" + str(bug_id) + "*"
        copy_command = "mv  " + regex_for_fix + " " + dir_results + ";"
        execute_command(copy_command)
        return

