import os
import re
import shutil

from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container


class VulnFix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(VulnFix, self).__init__(self.name)


    def repair(self, bug_info, config_info):
        super(VulnFix, self).repair(bug_info, config_info)
        ''' 
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output 
        '''

        dir_vulnfix_root = "/home/yuntong/vulnfix"
        dir_vulnfix_exist = self.is_dir(dir_vulnfix_root)
        if not dir_vulnfix_exist:
            emitter.error(
                "[Exception] Vulnfix repo is not at the expected location. "
                "Please double check whether we are in VulnFix container.")
            error_exit("Unhandled exception")

        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]

        # get ready the config file
        config_path = self.populate_config_file(dir_expr, dir_setup, experiment_info,
                                                container_id, dir_output)

        # actually start running
        timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
        execute_command(timestamp_command)

        vulnfix_command = "python3.8 src/main.py {0} {1}".format(additional_tool_param, config_path)
        status = self.run_command(vulnfix_command, self.log_output_path, dir_vulnfix_root, container_id)
        if status != 0:
            emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        timestamp_command = "printf \"\\n\" >> " + self.log_output_path
        timestamp_command += ";echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
        execute_command(timestamp_command)


    def populate_config_file(self, experiment_info):
        """
        Some fields of the VulnFix config file contains information which overlaps with what
        Cerberus already has, and also some of the fields depends on actual paths in the system. These fields are populated here into the existing config file template.
        """
        # (1) source-dir
        dir_src = os.path.join(self.dir_expr, "src")
        line_source_dir = "source-dir=" + dir_src + "\n"
        # (2) binary
        rel_binary_path = experiment_info[definitions.KEY_BINARY_PATH]
        binary_path = os.path.join(dir_src, rel_binary_path)
        line_binary = "binary=" + binary_path + "\n"
        # (3) cmd
        cmd = experiment_info[definitions.KEY_CRASH_CMD]
        cmd = cmd.replace("$POC", "<exploit>")
        line_cmd = "cmd=" + cmd + "\n"
        # (4) exploit
        dir_tests = os.path.join(self.dir_setup, "tests")
        list_dir_tests = self.list_dir(dir_tests)
        tests_list = [ os.path.join(dir_tests, t) for t in  list_dir_tests]
        if not tests_list:
            emitter.error("[Exception] there needs to be at least 1 exploit (failing) input!")
            error_exit("Unhandled Exception")
        exploit_path = sorted(tests_list)[0]
        line_exploit = "exploit=" + exploit_path + "\n"
        # (5) (OPTIONAL) normal-in
        line_normals = ""
        dir_normal_in = os.path.join(self.dir_setup, "vulnfix", "normals")
        normals_list = self.list_dir(dir_normal_in)

        if normals_list:
            line_normals = "normal-in=" + ",".join(normals_list) + "\n"
        # (6) runtime-dir
        line_runtime_dir = "runtime-dir=" + self.dir_output + "\n"

        # the config template should have been copied here
        config_path = os.path.join(self.dir_expr, "vulnfix", "config")
        config_updates = list()
        config_updates.append(line_binary)
        config_updates.append(line_cmd)
        config_updates.append(line_exploit)
        if line_normals:
            config_updates.append(line_normals)
        config_updates.append(line_runtime_dir)
        config_updates.append(line_source_dir)
        self.append_file(config_updates, config_path)
        return config_path


    def save_artefacts(self):
        """
        Save useful things from VulnFix execution result to the output folder.
        """
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_output = dir_info["output"]
        #
        # file_result = os.path.join(dir_results, "vulnfix.result")
        # file_patch = os.path.join(dir_results, "vulnfix.patch")
        # file_log_info = os.path.join(dir_results, "vulnfix.log.info")
        # file_log_debug = os.path.join(dir_results, "vulnfix.log.debug")
        #
        # copy_command = "cp {} {};".format(file_result, dir_output)
        # copy_command += "cp {} {};".format(file_patch, os.path.join(dir_output, "patches"))
        # copy_command += "cp {} {};".format(file_log_info, dir_output)
        # copy_command += "cp {} {}".format(file_log_debug, dir_output)
        #
        # self.run_command(copy_command, "/dev/null", "/", container_id)
        super().save_artefacts(dir_info, experiment_info, container_id)
        return


    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_logs = dir_info["log"]
        dir_results = dir_info["result"]
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = os.path.join(dir_logs, conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log")

        # parse this file for time info
        regex = re.compile('(.*-output.log$)')
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = os.path.join(dir_results, file)
                    break
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        time_duration = 0
        count_generated = 0
        time_start = 0
        time_validation = 0
        time_build = 0
        time_latency_compilation = 0
        time_latency_validation = 0
        time_latency_plausible = 0

        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)

        is_error = False
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r", encoding="iso-8859-1") as log_file:
                log_lines = log_file.readlines()
                time_start = log_lines[0].replace("\n", "")
                time_end = log_lines[-1].replace("\n", "")
                time_duration = self.time_duration(time_start, time_end)
                for line in log_lines:
                    if "Generating patch" in line:
                        count_plausible += 1
                        count_enumerations += 1

        # check whether a patch file is there
        count_generated = len([name for name in os.listdir(dir_results) if os.path.isfile(name) and ".patch" in name])


        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if values.DEFAULT_DUMP_PATCHES:
                count_enumerations = count_plausible
            else:
                log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
                log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))

        patch_space_info = (size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
        time_info = (time_build, time_validation, time_duration, time_latency_plausible,
                     time_latency_validation, time_latency_compilation, time_start)
        return patch_space_info, time_info
