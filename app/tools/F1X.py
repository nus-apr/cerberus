import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter
from os import listdir
from os.path import isfile, join
from datetime import datetime


class F1X(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(F1X, self).__init__(self.name)

    def generate_test_driver(self, dir_setup, container_id):
        test_script_path = dir_setup + "/test.sh"
        test_driver_path = dir_setup + "/f1x-test"
        tmp_driver_file = "/tmp/f1x-driver"
        if not os.path.isfile(tmp_driver_file):
            open(tmp_driver_file, "w")
        with open(tmp_driver_file, "r+") as res_file:
            res_file.seek(0)
            res_file.writelines("#!/bin/bash\n")
            res_file.writelines("bash {0} /experiment $@".format(test_script_path))
            res_file.truncate()
        perm_command = "chmod +x {}".format(tmp_driver_file)
        execute_command(perm_command)
        if container_id:
            copy_command = "docker cp " + tmp_driver_file + " " + container_id + ":" + test_driver_path
        else:
            copy_command = "cp " + tmp_driver_file + " " + test_driver_path
        execute_command(copy_command)

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
            additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
            self.generate_test_driver(dir_setup, container_id)
            test_driver_path = dir_setup + "/f1x-test"
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

            timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)
            repair_command = "timeout -k 5m {}h f1x ".format(str(timeout))
            repair_command += " -f {0} ".format(abs_path_buggy_file)
            repair_command += " -t {0} ".format(test_id_list)
            repair_command += " -T 15000"
            repair_command += " --driver={0} ".format(test_driver_path)
            repair_command += " -b \"{0} /experiment \"".format(build_script_path)
            if values.DEFAULT_DUMP_PATCHES:
                repair_command += " --output-space patch-space "
            dry_command = repair_command + " --disable-dteq"
            self.run_command(dry_command, self.log_output_path, dir_expr, container_id)
            all_command = repair_command + " --enable-assignment --disable-dteq --enable-validation  -a -o patches -v "
            if additional_tool_param:
                all_command = all_command + " " + additional_tool_param
            status = self.run_command(all_command, self.log_output_path, dir_expr, container_id)
            # repair_command = repair_command + "--enable-validation --disable-dteq  -a -o patches-top --output-top 10 -v"
            # status = self.run_command(repair_command, self.log_output_path, dir_expr, container_id)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

            if values.DEFAULT_DUMP_PATCHES:
                self.create_patches_from_space(dir_expr, fix_file, container_id)
            timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)
        return

    def create_patches_from_space(self, dir_exp, source_file, container_id):
        script_name = "{}/{}-dump-patches.py".format(dir_exp, self.name)
        abs_path_buggy_file = dir_exp + "/src/" + source_file
        dump_command = "python3 {} {} {}".format(script_name, abs_path_buggy_file, dir_exp)
        self.run_command(dump_command, self.log_output_path, dir_exp, container_id)

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_expr = dir_info["experiment"]
        dir_artifact = dir_info["artifact"]
        dir_patch_gen = dir_expr + "/patches"
        save_command = "cp -rf " + dir_patch_gen + " " + dir_artifact
        self.run_command(save_command, "/dev/null", "/", container_id)
        super(F1X, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def compute_latency_tool(self, start_time_str, end_time_str):
        # Fri 08 Oct 2021 04:59:55 PM +08
        # 2022-Apr-07 04:38:46.994352
        fmt_1 = '%a %d %b %Y %H:%M:%S %p'
        fmt_2 = '%Y-%b-%d %H:%M:%S.%f'
        start_time_str = start_time_str.split(" +")[0].strip()
        end_time_str = end_time_str.split(" +")[0].strip()
        tstart = datetime.strptime(start_time_str, fmt_1)
        tend = datetime.strptime(end_time_str, fmt_2)
        duration = (tend - tstart).total_seconds()
        return duration

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        count_non_compilable = 0
        count_plausible = 0
        count_generated = 0
        size_search_space = 0
        count_enumerations = 0
        time_duration = 0
        time_build = 0
        time_validation = 0
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file):
                    self.log_output_path = dir_results + "/" + file
                    break
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        time_stamp_first = None
        with open(self.log_output_path, "r") as log_file:
            log_lines = log_file.readlines()
            time_stamp_start = log_lines[0].replace("\n", "")
            time_stamp_end = log_lines[-1].replace("\n", "")
            time_duration = self.time_duration(time_stamp_start, time_stamp_end)
            for line in log_lines:
                if "candidates evaluated: " in line:
                    count = line.split("candidates evaluated: ")[-1].strip().replace("\n", "")
                    if str(count).isnumeric():
                        count_enumerations = int(count)
                elif "validation time: " in line:
                    time = line.split("validation time: ")[-1].strip().replace("\n", "")
                    time_validation += float(time)
                elif "build time: " in line:
                    time = line.split("build time: ")[-1].strip().replace("\n", "")
                    time_build += float(time)
                elif "validating patch " in line:
                    count_enumerations += 1
                elif "search space size: " in line:
                    size_search_space = int(line.split("search space size: ")[-1])
                elif "plausible patches: " in line:
                    count_plausible = int(line.split("plausible patches: ")[-1])
                elif "failed to infer compile commands" in line:
                    size_search_space = -1
                elif "PASS" in line:
                    if time_stamp_first is None:
                        time_stamp_first = line.split("[debug]")[0].replace("[", "").replace("]", "")
            log_file.close()
        time_latency = 0
        if time_stamp_first:
            time_latency = self.compute_latency_tool(time_stamp_start, time_stamp_first)

        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        dir_patch = dir_results + "/patches"
        if dir_patch and os.path.isdir(dir_patch):
            output_patch_list = [f for f in listdir(dir_patch) if isfile(join(dir_patch, f))]
            count_generated = len(output_patch_list)
        if values.CONF_USE_VALKYRIE:
            dir_valid = dir_results + "/patch-valid"
            count_generated = 0
            time_first_patch = datetime.now().timestamp()
            if dir_valid and os.path.isdir(dir_valid):
                output_patch_list = [f for f in listdir(dir_valid) if isfile(join(dir_valid, f))]
                count_plausible = len(output_patch_list)
                for output_patch in output_patch_list:
                    modified_time = os.stat(output_patch).st_mtime
                    if modified_time < time_first_patch:
                        time_first_patch = modified_time
            time_latency = self.compute_latency_valkyrie(time_stamp_start, time_first_patch)

        count_implausible = (size_search_space - count_plausible) + (count_enumerations - count_generated)
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if not values.DEFAULT_DUMP_PATCHES:
                log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
                log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
                log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t count generated: {0}\n".format(count_generated))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time build: {0} seconds\n".format(time_build))
            log_file.write("\t\t time validation: {0} seconds\n".format(time_validation))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
            log_file.write("\t\t time latency: {0} seconds\n".format(time_latency))
        patch_space_info = (size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
        time_info = (time_build, time_validation, time_duration, time_latency)
        return patch_space_info, time_info
