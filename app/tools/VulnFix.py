import os
import re
import shutil

from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class VulnFix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(VulnFix, self).__init__(self.name)


    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id, container_id, source_file):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = os.path.join(dir_logs,
            conf_id + "-" + self.name + "-" + bug_id + "-instrument.log")
        # TODO: try with one instrumentation script
        instrumentation_script_path = os.path.join(dir_setup, self.name.lower(), "instrument.sh")
        instrumentation_exist = os.path.isfile(instrumentation_script_path)
        if not instrumentation_exist:
            return
        # do real instrumentation now
        command_str = "bash instrument.sh {}".format(dir_expr)
        dir_setup_exp = os.path.join(dir_setup, self.name.lower())
        rc = self.run_command(command_str, self.log_instrument_path, dir_setup_exp, container_id)
        if rc != 0:
            error_exit("error with instrumentation of ", self.name)


    def populate_config_file(self, dir_expr, dir_setup, experiment_info):
        """
        Some fields of the VulnFix config file contains information which overlaps with what
        Cerberus already has, and also some of the fields depends on actual paths in the system. These fields are populated here into the existing config file template.
        """
        # (1) source-dir
        dir_src = os.path.join(dir_expr, "src")
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
        dir_tests = os.path.join(dir_setup, "tests")
        tests_list = [ os.path.join(dir_tests, t) for t in os.listdir(dir_tests) ]
        if not tests_list:
            emitter.error("[Exception] there needs to be at least 1 exploit (failing) input!")
            error_exit("Unhandled Exception")
        exploit_path = sorted(tests_list)[0]
        line_exploit = "exploit=" + exploit_path + "\n"
        # (5) (OPTIONAL) normal-in
        line_normals = ""
        dir_normal_in = os.path.join(dir_setup, "vulnfix", "normals")
        if os.path.isdir(dir_normal_in):
            normals_list = [ os.path.join(dir_normal_in, t) for t in os.listdir(dir_normal_in) ]
            if normals_list:
                line_normals = "normal-in=" + ",".join(normals_list) + "\n"
        # (6) runtime-dir
        dir_runtime = os.path.join(dir_expr, "vulnfix", "runtime")
        line_runtime_dir = "runtime-dir=" + dir_runtime + "\n"

        # the config template should have been copied here
        config_path = os.path.join(dir_expr, "vulnfix", "config")

        with open(config_path, "a") as f:
            f.write(line_binary)
            f.write(line_cmd)
            f.write(line_exploit)
            if line_normals:
                f.write(line_normals)
            f.write(line_runtime_dir)
            f.write(line_source_dir)

        return config_path


    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        super(VulnFix, self).repair(dir_info, experiment_info, config_info, container_id, instrument_only)
        if instrument_only:
            return
        emitter.normal("\t\t\t running repair with " + self.name)
        dir_vulnfix_root = "/home/yuntong/vulnfix"
        if not os.path.isdir(dir_vulnfix_root):
            emitter.error("[Exception] Vulnfix repo is not at the expected location. Please double check whether we are in VulnFix container.")
            error_exit("Unhandled exception")

        conf_id = config_info[definitions.KEY_ID]
        dir_logs = dir_info["logs"]
        dir_setup = dir_info["setup"]
        dir_expr = dir_info["expr"]
        bug_id = str(experiment_info[definitions.KEY_BUG_ID])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = os.path.join(dir_logs,
            conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log")

        # get ready the config file
        config_path = self.populate_config_file(dir_expr, dir_setup, experiment_info)

        if container_id:
            emitter.error("[Exception] unimplemented functionality: VulnFix docker support not implemented")
            error_exit("Unhandled Exception")

        # actually start running
        timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
        execute_command(timestamp_command)

        vulnfix_command = "cd {};".format(dir_vulnfix_root)
        vulnfix_command += "python3.8 src/main.py {0} {1}".format(additional_tool_param, config_path)
        status = execute_command(vulnfix_command)
        if status != 0:
            emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        timestamp_command = "printf \"\\n\" >> " + self.log_output_path
        timestamp_command += ";echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
        execute_command(timestamp_command)


    def save_artefacts(self, dir_info, experiment_info, container_id):
        """
        Save useful things from VulnFix execution result to the output folder.
        """
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_exp = dir_info["experiment"]
        dir_output = dir_info["output"]
        dir_runtime = os.path.join(dir_exp, "vulnfix", "runtime")

        file_result = os.path.join(dir_runtime, "vulnfix.result")
        file_patch = os.path.join(dir_runtime, "vulnfix.patch")
        file_log_info = os.path.join(dir_runtime, "vulnfix.log.info")
        file_log_debug = os.path.join(dir_runtime, "vulnfix.log.debug")

        shutil.copy2(file_result, dir_output)
        shutil.copy2(file_patch, os.path.join(dir_output, "patches"))
        shutil.copy2(file_log_info, dir_output)
        shutil.copy2(file_log_debug, dir_output)

        return super().save_artefacts(dir_info, experiment_info, container_id)

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
        time_first = 0
        time_latency = 0
        time_validation = 0
        time_build = 0

        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)


        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r", encoding="iso-8859-1") as log_file:
                log_lines = log_file.readlines()
                time_start = log_lines[0].replace("\n", "")
                time_end = log_lines[-1].replace("\n", "")
                time_duration = self.time_duration(time_start, time_end)

        # check whether a patch file is there
        dir_patches = os.path.join(dir_results, "patches")
        count_generated = len([name for name in os.listdir(dir_patches) if os.path.isfile(name)])
        count_plausible = count_generated

        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if values.DEFAULT_DUMP_PATCHES:
                count_enumerations = count_plausible
            else:
                log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))

            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
        patch_space_info = (size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
        time_info = (time_build, time_validation, time_duration, time_latency, time_first)
        return patch_space_info, time_info
