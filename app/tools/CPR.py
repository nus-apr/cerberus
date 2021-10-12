import os
import shutil
import re
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class CPR(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(CPR, self).__init__(self.name)


    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg,
               container_id):
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        conf_path = dir_expr + "/cpr/repair.conf"
        timeout_m = str(int(timeout) * 60)
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + ","
        seed_id_list = ""
        if passing_test_list:
            for test_id in passing_test_list:
                seed_id_list += test_id + ","
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        cpr_command = "timeout -k 5m {0}h cpr --conf=".format(timeout) + conf_path + " "
        cpr_command += " --seed-id-list=" + seed_id_list + " "
        cpr_command += " --test-id-list=" + test_id_list + " "
        cpr_command += "{0} --time-duration={1} >> {2} 2>&1 ".format(additional_tool_param, str(timeout_m),
                                                                     self.log_output_path)
        status = execute_command(cpr_command)
        if status != 0:
            emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_logs(self, dir_results, dir_expr, dir_setup, bug_id):
        super(CPR, self).save_logs(dir_results, dir_expr, dir_setup, bug_id)
        dir_logs = "/CPR/logs/" + bug_id
        execute_command("cp -rf" + dir_logs + " " + dir_results + "/logs")

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_setup = dir_info["setup"]
        dir_results = dir_info["result"]
        bug_id = str(experiment_info[definitions.KEY_BUG_ID])
        dir_patches = "/CPR/output/" + bug_id
        if os.path.isdir(dir_patches):
            execute_command("cp -rf " + dir_patches + " " + dir_results + "/patches")
        shutil.copy(dir_setup + "/cpr/instrument.sh", dir_results)
        super(CPR, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def post_process(self, dir_expr, dir_results):
        emitter.normal("\t\t\t post-processing for {}".format(self.name))
        super(CPR, self).post_process(dir_expr, dir_results)
        clean_command = "rm -rf " + dir_results + "/patches/klee-out-*"
        execute_command(clean_command)

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
        time_duration = 0
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        is_timeout = True
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r") as log_file:
                log_lines = log_file.readlines()
                time_start = log_lines[0].replace("\n", "")
                time_end = log_lines[-1].replace("\n", "")
                time_duration = self.time_duration(time_start, time_end)
                for line in log_lines:
                    if "|P|=" in line:
                        count_plausible = int(line.split("|P|=")[-1].strip().replace("^[[0m", "").split(":")[0])
                    elif "number of concrete patches explored" in line:
                        count_enumerations = int(line.split("number of concrete patches explored: ")[-1].strip().split("\x1b")[0].split(".0")[0])
                        size_search_space = count_enumerations
                    elif "Runtime Error" in line:
                        is_error = True
                    elif "statistics" in line:
                        is_timeout = False

                log_file.close()
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_timeout:
            emitter.warning("\t\t\t\t[warning] timeout before ending")
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if values.DEFAULT_DUMP_PATCHES:
                count_enumerations = count_plausible
            else:
                log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
                log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
                log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration

    def pre_process(self, dir_logs, dir_expr, dir_setup):
        emitter.normal("\t\t\t pre-processing for {}".format(self.name))
        super(CPR, self).pre_process(dir_logs, dir_expr, dir_setup)
        if not os.path.isdir("/tmp"):
            os.mkdir("/tmp")
        return
