import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class Angelix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()

    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        if os.path.isfile(dir_setup + "/{}/instrument.sh".format(self.name.lower())):
            if not os.path.isfile(dir_setup + "/src/INSTRUMENTED"):
                command_str = "cd " + dir_setup + "/{0}; bash instrument.sh {1}".format(self.name.lower(), dir_expr)
                command_str += " > {0} 2>&1".format(self.log_instrument_path)
                status = execute_command(command_str)
                if not status == 0:
                    error_exit("error with instrumentation of ", self.name)
                with open(dir_expr + "/src/INSTRUMENTED", 'w') as fp:
                    pass
        else:
            error_exit("no instrumentation available for ", self.name)
        return

    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        line_number = ""
        if fix_location:
            source_file, line_number = fix_location.split(":")
        else:
            with open(dir_expr + "/manifest.txt", "r") as man_file:
                source_file = man_file.readlines()[0].strip().replace("\n", "")

        src_path = dir_expr + "/src"
        gold_path = dir_expr + "/src-gold"
        angelix_dir_path = dir_expr + '/angelix'
        oracle_path = angelix_dir_path + "/oracle"
        config_script_path = angelix_dir_path + '/config'
        build_script_path = angelix_dir_path + '/build'
        timeout_s = int(timeout) * 3600
        syn_timeout = int(0.25 * timeout_s * 1000)
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + " "
        if passing_test_list:
            for test_id in passing_test_list:
                test_id_list += test_id + " "

        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        angelix_command = "timeout -k 5m {8}h  angelix {0} {1} {2} {3}  " \
                          "--configure {4}  " \
                          "--golden {5}  " \
                          "--build {6} " \
                          "--synthesis-timeout {7} ".format(src_path, source_file, oracle_path,
                                                            test_id_list, config_script_path, gold_path,
                                                            build_script_path, str(syn_timeout), str(timeout))

        if fix_location:
            angelix_command += " --lines {0}  ".format(line_number)

        if os.getenv("ANGELIX_ARGS", False):
            angelix_command += " " + os.environ["ANGELIX_ARGS"] + " "

        angelix_command += "  --generate-all {0} " \
                           " --timeout {1} >> {2} 2>&1 ".format(additional_tool_param, str(timeout_s), self.log_output_path)
        status = execute_command(angelix_command)
        if status != 0:
            emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        self.save_logs(dir_results, dir_expr, dir_setup, bug_id)
        dir_patches = dir_expr + "/src/repair"
        if os.path.isdir(dir_patches):
            execute_command("cp -rf " + dir_patches + " " + dir_results + "/patches")
        return

    def post_process(self, dir_expr, dir_results):
        emitter.normal("\t\t\t post-processing for {}".format(self.name))
        super(Angelix, self).post_process(dir_expr, dir_results)
        clean_command = "rm -rf /tmp/* /experiments/.angelix/"
        execute_command(clean_command)

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id):
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
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r") as log_file:
                log_lines = log_file.readlines()
                for line in log_lines:
                    if "candidate fix synthesized" in line:
                        count_plausible = count_plausible + 1
                    elif "selected expressions" in line:
                        size_search_space = size_search_space + 1
                    elif "considering suspicious expressions" in line:
                        count_enumerations = count_enumerations + 1
                    elif "repair test suite: []" in line:
                        is_error = True
                        emitter.warning("\t\t\t\t[warning] repair test suite: []")
                    elif "validation test suite: []" in line:
                        is_error = True
                        emitter.warning("\t\t\t\t[warning] validation test suite: []")
                    elif "No negative test exists" in line:
                        is_error = True
                        emitter.warning("\t\t\t\t[warning] No negative test exists")
                log_file.close()
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable
