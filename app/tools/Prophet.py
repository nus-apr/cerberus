import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
from os import listdir
from os.path import isfile, join


class Prophet(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        test_config_str = "-\n"
        test_config_str += "-\n"
        test_config_str += "Diff Cases: Tot {0}\n".format(len(failing_test_list))
        for test_id in failing_test_list:
            if test_id == failing_test_list[-1]:
                test_config_str += test_id + "\n"
            else:
                test_config_str += test_id + " "
        test_config_str += "Positive Cases: Tot {0}\n".format(len(passing_test_list))
        if passing_test_list:
            filtered_list = self.filter_tests(passing_test_list, subject_name, bug_id)
            for test_id in filtered_list:
                if test_id == filtered_list[-1]:
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

        repair_command = "timeout -k 5m {0}h prophet -feature-para /prophet-gpl/crawler/para-all.out ".format(timeout)
        repair_command += " -full-synthesis -full-explore "
        repair_command += " -r {0}".format(dir_expr + "/workdir")
        repair_command += " -cond-ext -replace-ext -skip-verify "
        repair_command += " -timeout {0} ".format(int(timeout))
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
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
        regex_for_fix = "*-fix-" + str(bug_id) + "*"
        copy_command = "mv  " + regex_for_fix + " " + dir_results
        execute_command(copy_command)
        return

    def filter_tests(self, test_id_list, subject, bug_id):
        filtered_list = []
        filter_list = []
        if str(subject).lower() == "python":
            filter_list = []
            if bug_id == "69935":
                filter_list.extend([157, 158, 159, 160, 161, 163, 164, 162, 60, 70, 98, 156,151, 152 ,153 ,155])
        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return filtered_list

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file):
                    self.log_output_path = dir_results + "/" + file
                    break
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r", encoding='iso-8859-1') as log_file:
                log_lines = log_file.readlines()
                for line in log_lines:
                    if "number of explored templates:" in line:
                        count_enumerations = int(line.split("number of explored templates: ")[-1])
                    elif "Single building" in line and "failed as well!" in line:
                        count_non_compilable = count_non_compilable + 1
                    elif "different repair candidate" in line:
                        size_search_space = int(line.split(" different repair candidate")[0].replace("Total ", "").strip())
                    elif "Segmentation fault" in line:
                        is_error = True
                    elif "Verification failed!" in line or "Repair error:" in line:
                        emitter.warning("\t\t\t\t[warning] verification error detected in test suite")
                log_file.close()
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if os.path.isdir(dir_results):
            output_patch_list = [f for f in listdir(dir_results) if isfile(join(dir_results, f)) and ".c" in f]
            count_plausible = len(output_patch_list)
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable
