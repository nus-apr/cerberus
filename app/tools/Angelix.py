import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
from os import listdir
from os.path import isfile, join


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
            filtered_list = self.filter_tests(passing_test_list, subject_name, bug_id)
            for test_id in filtered_list:
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

        if os.path.isfile("/tmp/ANGELIX_ARGS"):
            with open("/tmp/ANGELIX_ARGS", "r") as arg_file:
                arg_line = arg_file.readline()
                angelix_command += " " + arg_line.strip() + " "
            os.remove("/tmp/ANGELIX_ARGS")
        if os.path.isfile("/tmp/ANGELIX_KLEE_LOAD"):
            with open("/tmp/ANGELIX_KLEE_LOAD", "r") as arg_file:
                load_line = arg_file.readline()
                os.system("export ANGELIX_KLEE_LOAD={}".format(load_line.strip()))
            os.remove("/tmp/ANGELIX_KLEE_LOAD")
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
        copy_command = "mv src-2021-* " + dir_results + "/patches"
        execute_command(copy_command)
        return

    def post_process(self, dir_expr, dir_results):
        emitter.normal("\t\t\t post-processing for {}".format(self.name))
        super(Angelix, self).post_process(dir_expr, dir_results)
        clean_command = "rm -rf /tmp/* /experiments/.angelix/"
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
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        is_timeout = True
        reported_fail_list = set()
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r") as log_file:
                log_lines = log_file.readlines()
                collect_neg = False
                for line in log_lines:
                    if "selected expressions" in line:
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
                        is_timeout = False
                        emitter.warning("\t\t\t\t[warning] No negative test exists")
                    elif "no patch generated" in line:
                        is_timeout = False
                        count_plausible = 0
                    elif "patches successfully generated" in line:
                        is_timeout = False
                    elif "running negative tests" in line:
                        collect_neg = True
                    elif collect_neg and "running test" in line:
                        t_id = line.split("running test ")[-1].split(" ")[0].replace("'", "")
                        reported_fail_list.add(t_id)
                    elif collect_neg and "repair test suite" in line:
                        collect_neg = False
                log_file.close()
        dir_patch = dir_results + "/patches"
        if dir_patch and os.path.isdir(dir_patch):
            output_patch_list = [f for f in listdir(dir_patch) if isfile(join(dir_patch, f))]
            count_plausible = len(output_patch_list)
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        if list(reported_fail_list) != fail_list:
            emitter.warning("\t\t\t\t[warning] unexpected failing test-cases reported")
            emitter.warning("\t\t\t\texpected fail list: {0}".format(",".join(fail_list)))
            reported_list_str = ",".join(list(reported_fail_list))
            if len(reported_fail_list) > 10:
                reported_list_str = ",".join(list(reported_fail_list)[:10]) + "..."
            emitter.warning("\t\t\t\treported fail list: {0}".format(reported_list_str))
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_timeout:
            emitter.warning("\t\t\t\t[warning] timeout before ending")
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable

    def pre_process(self, dir_logs, dir_expr, dir_setup):
        emitter.normal("\t\t\t pre-processing for {}".format(self.name))
        super(Angelix, self).pre_process(dir_logs, dir_expr, dir_setup)
        if not os.path.isdir("/tmp"):
            os.mkdir("/tmp")
        return

    def filter_tests(self, test_id_list, subject, bug_id):
        filtered_list = []
        filter_list = []
        if str(subject).lower() == "gzip":
            filter_list = []
            if bug_id == "884ef6d16c":
                filter_list.extend([4, 11])

        # elif str(subject).lower() == "php":
        #     filter_list = []
        #     if bug_id == "5bb0a44e06":
        #         filter_list.extend([5553, 6548, 9563, 280, 3471])
        #     elif bug_id == "0927309852":
        #         filter_list.extend([7384, 7440, 7551, 7511, 7527, 7639, 9563, 7780])

        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return filtered_list