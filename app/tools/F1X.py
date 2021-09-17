import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class F1X(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(F1X, self).__init__(self.name)

    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        super(F1X, self).repair(dir_info, experiment_info, config_info, container_id, instrument_only)
        if not instrument_only:
            emitter.normal("\t\t\t running repair with " + self.name)
            conf_id = config_info[definitions.KEY_ID]
            dir_logs = dir_info["logs"]
            dir_setup = dir_info["setup"]
            dir_expr = dir_info["expr"]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            fix_file = experiment_info[definitions.KEY_FIX_FILE]
            fix_location = experiment_info[definitions.KEY_FIX_LOC]
            passing_test_list = experiment_info[definitions.KEY_PASSING_TEST]
            failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
            timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
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
                abs_path_buggy_file = dir_expr + "/src/" + fix_file

            timestamp_command = "echo $(date) >> " + self.log_output_path
            execute_command(timestamp_command)
            repair_command = "timeout -k 5m {}h f1x ".format(str(timeout))
            repair_command += " -f {0} ".format(abs_path_buggy_file)
            repair_command += " -t {0} ".format(test_id_list)
            repair_command += " -T 15000"
            repair_command += " --driver={0} ".format(test_driver_path)
            repair_command += " -b {0} ".format(build_script_path)
            dry_command = repair_command + " --disable-dteq"
            self.run_command(dry_command, self.log_output_path, dir_expr, container_id)
            all_command = repair_command + " --disable-dteq  -a -o patches -v "
            status = self.run_command(all_command, self.log_output_path, dir_expr, container_id)
            # repair_command = repair_command + "--enable-validation --disable-dteq  -a -o patches-top --output-top 10 -v"
            # status = self.run_command(repair_command, self.log_output_path, dir_expr, container_id)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

            timestamp_command = "echo $(date) >> " + self.log_output_path
            execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_expr = dir_info["experiment"]
        dir_artifact = dir_info["artifact"]
        dir_patches = dir_expr + "/patches"
        save_command = "cp -rf " + dir_patches + " " + dir_artifact
        self.run_command(save_command, "/dev/null", "/", container_id)
        super(F1X, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
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
        with open(self.log_output_path, "r") as log_file:
            log_lines = log_file.readlines()
            for line in log_lines:
                if "candidates evaluated: " in line:
                    count_enumerations = int(line.split("candidates evaluated: ")[-1])
                elif "search space size: " in line:
                    size_search_space = int(line.split("search space size: ")[-1])
                elif "plausible patches: " in line:
                    count_plausible = int(line.split("plausible patches: ")[-1])
                elif "failed to infer compile commands" in line:
                    size_search_space = -1
            log_file.close()
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable
