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
            filtered_list = self.filter_tests(passing_test_list, subject_name, bug_id)
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

    def filter_tests(self, test_id_list, subject, bug_id):
        filtered_list = []
        filter_list = []
        if str(subject).lower() == "python":
            filter_list = [87, 172, 209, 222, 226]
            if bug_id == "69372":
                filter_list.extend([240, 322, 323, 324])
            elif bug_id == "69935":
                filter_list.extend([240, 322, 323, 324])
            elif bug_id == "69935":
                filter_list.extend([240, 322, 323, 324])

        elif str(subject).lower() == "php":
            filter_list = []
            if bug_id == "5bb0a44e06":
                filter_list.extend([5553, 6548, 9563, 280, 3471])
            elif bug_id == "0927309852":
                filter_list.extend([7384, 7440, 7551, 7511, 7527, 7639, 9563, 7780])
            elif bug_id == "1e91069eb4":
                filter_list.extend([404, 6633, 6777, 7049, 7612, 8695, 8766, 1597, 3908, 6948])
            elif bug_id == "1f49902999":
                filter_list.extend([5553, 6110, 6472, 6475, 6478, 6485, 6489, 6494, 6501, 6503, 6507, 6853, 7165, 9563, 3471, 10638])
            elif bug_id == "b84967d3e2":
                filter_list.extend([5553, 9563])
            elif bug_id == "1d984a7ffd":
                filter_list.extend([3339, 5553, 9563, 3471, 10638])
            elif bug_id == "6e74d95f34":
                filter_list.extend([5553, 9563, 3471, 10638, 2298])
            elif bug_id == "8deb11c0c3":
                filter_list.extend([404, 6633, 6777, 7049, 7615, 8695, 8766, 1597, 6948])
            elif bug_id == "2adf58cfcf":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 280, 3471, 10638])
            elif bug_id == "3acdca4703":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471, 7527, 10638, 6512])
            elif bug_id == "5a8c917c37":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471, 5137, 6336, 9617])
            elif bug_id == "2e25ec9eb7":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 10569, 280, 3471, 10638])
            elif bug_id == "77ed819430":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471, 10638])
            elif bug_id == "efcb9a71cd":
                filter_list.extend([404, 6633, 6777, 7049, 8695, 8766, 303, 1778, 3908, 6948])
            elif bug_id == "09b990f499":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563])
            elif bug_id == "821d7169d9":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
            elif bug_id == "daecb2c0f4":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563])
            elif bug_id == "964f44a280":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
            elif bug_id == "1056c57fa9":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
            elif bug_id == "05c5c8958e":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
            elif bug_id == "d4ae4e79db":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 3575, 6219])
            elif bug_id == "b5f15ef561":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
            elif bug_id == "2e5d5e5ac6":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
            elif bug_id == "9b86852d6e":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 10578, 10976, 11133, 11135, 3575, 6219])
            elif bug_id == "c1e510aea8":
                filter_list.extend([3940, 4144, 5912, 5921, 6648, 9787, 6219, 3575])
            elif bug_id == "fb37f3b20d":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 3575, 4149, 6219, 6648])
            elif bug_id == "13ba2da5f6":
                filter_list.extend([3940, 4144, 5912, 5921, 6028, 6061, 6072, 9787, 9834, 3442])
            elif bug_id == "3c7a573a2c":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
            elif bug_id == "bc810a443d":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 10160, 11381, 11682, 11713])
            elif bug_id == "d3b20b4058":
                filter_list.extend([3940, 4144, 5912, 5921, 9787])
            elif bug_id == "f330c8ab4e":
                filter_list.extend([3940, 4144, 5912, 5921, 9787])
            elif bug_id == "b548293b99":
                filter_list.extend([418, 7062, 7333, 8997, 9069, 7232, 9267])
            elif bug_id == "db0888dfc1":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
            elif bug_id == "dfa08dc325":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 3442, 3575, 6219])
            elif bug_id == "52c36e60c4":
                filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 2400, 3390])
            elif bug_id == "acaf9c5227":
                filter_list.extend([3958, 4162, 5936, 5945, 9824, 3593, 6245, 6247, 6681])
            elif bug_id == "6672171672":
                filter_list.extend([3958, 4162, 5936, 5945, 9824, 9871, 3593, 6245])
            elif bug_id == "34fe62619d":
                filter_list.extend([325, 418, 963, 7200, 7471, 9145, 9216, ])
            elif bug_id == "cdc512afb3":
                filter_list.extend([4017, 4221, 6004, 6013, 9983, 10030, 2472, 3465, 3506, 3518, 3524])
            elif bug_id == "d4f05fbffc":
                filter_list.extend([4017, 4221, 6004, 6013, 9983, 3650, 6314])
            elif bug_id == "efc94f3115":
                filter_list.extend([4017, 4221, 6004, 6013, 9983, 10030, 3650, 5572, 6052, 6314])
            elif bug_id == "7337a901b7":
                filter_list.extend([4017, 4221, 6004, 6013, 9983, 3650, 6314])
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
        is_timeout = True
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
                elif "patches successfully generated" in line:
                    is_timeout = False
                elif "no patch found" in line:
                    is_timeout = False
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
                    elif "At-risk data found" in line:
                        is_error = True
                        emitter.error("\t\t\t\t[error] previous results have corrupted")
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_timeout:
            emitter.warning("\t\t\t\t[warning] timeout detected")
        if reported_failing_test != fail_list and reported_failing_test and not is_timeout:
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

    def pre_process(self, dir_logs, dir_expr, dir_setup):
        emitter.normal("\t\t\t pre-processing for {}".format(self.name))
        super(Fix2Fit, self).pre_process(dir_logs, dir_expr, dir_setup)
        if os.path.isdir(dir_setup + "/out"):
            shutil.rmtree(dir_setup + "/out")
        if os.path.isdir(dir_setup + "/patches"):
            shutil.rmtree(dir_setup + "/patches")
        if os.path.isdir(dir_setup + "/seed-dir"):
            shutil.rmtree(dir_setup + "/seed-dir")
        return
