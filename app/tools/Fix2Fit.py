import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
from os import listdir
from os.path import isfile, join


class Fix2Fit(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        abs_path_binary = dir_expr + "/src/" + binary_path
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + " "
        if passing_test_list:
            filtered_list = self.filter_tests(passing_test_list, subject_name)
            for test_id in filtered_list:
                test_id_list += test_id + " "

        if fix_location:
            abs_path_buggy_file = dir_expr + "/src/" + fix_location
        else:
            with open(dir_expr + "/manifest.txt", "r") as man_file:
                abs_path_buggy_file = dir_expr + "/src/" + man_file.readlines()[0].strip().replace("\n", "")

        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        repair_command = "export SUBJECT_DIR={0}; ".format(dir_setup)
        repair_command += "export BUGGY_FILE={0}; ".format(abs_path_buggy_file)
        repair_command += "export TESTCASE=\"{0}\"; ".format(test_id_list)
        repair_command += "export DRIVER=./test.sh; "
        repair_command += "export BINARY={0}; ".format(abs_path_binary)
        repair_command += "export TIME_OUT={0}; ".format(abs_path_binary)
        repair_command += "export BINARY_INPUT=\"{0}\"; ".format(binary_input_arg)
        repair_command += "cd {0}; timeout -k 5m {1}h bash /src/scripts/run.sh ".format(dir_setup, str(timeout))
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
        dir_patches = dir_setup + "/patches"
        if os.path.isdir(dir_patches):
            execute_command("cp -rf " + dir_patches + " " + dir_results + "/patches")
        return

    def save_logs(self, dir_results, dir_expr, dir_setup, bug_id):
        super(Fix2Fit, self).save_logs(dir_results, dir_expr, dir_setup, bug_id)
        patch_gen_log = dir_setup + "/original.txt"
        shutil.copy(patch_gen_log, dir_results)

    def filter_tests(self, test_id_list, subject):
        filtered_list = []
        filter_list = []
        if str(subject).lower() == "python":
            filter_list = [87, 172, 209, 222, 226, 240, 322, 323, 324, 31, 157]
        elif str(subject).lower() == "php":
            filter_list = [3836, 4037, 5553, 5797, 5806, 9563]
        elif str(subject).lower() == "gmp":
            filter_list = [34]
        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return filtered_list

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        count_filtered = 0
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file):
                    self.log_output_path = dir_results + "/" + file
                    break
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        reported_failing_test = []
        with open(dir_results + "/original.txt", "r") as log_file:
            log_lines = log_file.readlines()
            for line in log_lines:
                if "candidates evaluated: " in line:
                    count_enumerations = int(line.split("candidates evaluated: ")[-1].strip())
                elif "search space size: " in line:
                    size_search_space = line.split("search space size: ")[-1].strip()
                elif "plausible patches: " in line:
                    count_plausible = int(line.split("plausible patches: ")[-1].strip())
                elif "negative tests: [" in line:
                    reported_failing_test = str(line).split("negative tests: [")[-1].split("]")[0].split(", ")
            log_file.close()
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, 'r', encoding='iso-8859-1') as log_file:
                log_lines = log_file.readlines()
                for line in log_lines:
                    if "Fail to execute f1x" in line:
                        is_error = False
                    elif "tests are not specified" in line:
                        is_error = True
                    elif "no negative tests" in line:
                        emitter.warning("\t\t\t\t[warning] no negative tests")
                    elif "failed to infer compile commands" in line:
                        is_error = True
                        emitter.error("\t\t\t\t[error] compilation command not found")
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if reported_failing_test != fail_list:
            emitter.warning("\t\t\t\t[warning] unexpected failing test-cases reported")
            emitter.warning("\t\t\t\texpected fail list: {0}".format(",".join(fail_list)))
            emitter.warning("\t\t\t\treported fail list: {0}".format(",".join(reported_failing_test)))

        dir_patch = dir_results + "/patches"
        if dir_patch and os.path.isdir(dir_patch):
            output_patch_list = [f for f in listdir(dir_patch) if isfile(join(dir_patch, f))]
            count_filtered = len(output_patch_list)

        count_implausible = count_enumerations - count_plausible - count_non_compilable
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count filtered patches: {0}\n".format(count_filtered))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable
