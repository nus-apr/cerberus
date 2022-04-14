import os
import re
import multiprocessing as mp
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container
import mmap
from os import listdir
from os.path import isfile, join
from datetime import datetime

class Darjeeling(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Darjeeling, self).__init__(self.name)

    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id, container_id, source_file):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        dir_expr_base = os.path.abspath(os.path.dirname(__file__) + "/../../experiments/")
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        instrumentation_script_path = "{0}/{1}/instrument.sh".format(dir_setup, self.name.lower())
        if container_id:
            instrumentation_exist = container.is_file(container_id, instrumentation_script_path)
        else:
            instrumentation_exist = os.path.isfile(instrumentation_script_path)
        if instrumentation_exist:
            command_str = "bash instrument.sh {0} {1}".format(dir_expr_base, source_file)
            dir_setup_exp = dir_setup + "/{}".format(self.name.lower())
            status = self.run_command(command_str, self.log_instrument_path, dir_setup_exp, container_id)
            if not status == 0:
                error_exit("error with instrumentation of ", self.name)
        return

    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        super(Darjeeling, self).repair(dir_info, experiment_info, config_info, container_id, instrument_only)
        if not instrument_only:
            conf_id = config_info[definitions.KEY_ID]
            dir_logs = dir_info["logs"]
            dir_setup = dir_info["setup"]
            dir_expr = dir_info["expr"]
            passing_test_list = experiment_info[definitions.KEY_PASSING_TEST]
            failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            emitter.normal("\t\t\t running repair with " + self.name)
            fix_file = experiment_info[definitions.KEY_FIX_FILE]
            fix_location = experiment_info[definitions.KEY_FIX_LOC]
            timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
            additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"

            dir_output = dir_info["output"]
            dir_patch = dir_output + "/patches"
            mkdir_command = "mkdir " + dir_patch
            self.run_command(mkdir_command, self.log_output_path, dir_expr, container_id)

            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
            execute_command(timestamp_command)

            repair_command = "timeout -k 5m {1}h  ".format(dir_expr + "/src", str(timeout))
            repair_command += "darjeeling repair --continue --patch-dir {} ".format(dir_patch)
            repair_command += " --threads {} ".format(mp.cpu_count())
            repair_command += additional_tool_param + " "
            if values.DEFAULT_DUMP_PATCHES:
                repair_command += " --dump-all "
            repair_command += " repair.yml".format(self.log_output_path)
            status = self.run_command(repair_command, self.log_output_path, dir_expr + "/src", container_id)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_expr = dir_info["experiment"]
        dir_results = dir_info["result"]
        dir_patch = dir_expr + "/src/patches"
        dir_output = dir_info["output"]
        dir_artifact = dir_info["artifact"]
        copy_command = "cp -rf  " + dir_patch + " " + dir_artifact
        self.run_command(copy_command, "/dev/null", dir_expr, container_id)

        super(Darjeeling, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def compute_latency_tool(self, start_time_str, end_time_str):
        # Fri 08 Oct 2021 04:59:55 PM +08
        # 2022-Apr-07 04:38:46.994352
        fmt_1 = '%a %d %b %Y %H:%M:%S %p'
        fmt_2 = '%Y-%m-%d %H:%M:%S.%f'
        start_time_str = start_time_str.split(" +")[0].strip()
        end_time_str = end_time_str.split(" +")[0].strip()
        tstart = datetime.strptime(start_time_str, fmt_1)
        tend = datetime.strptime(end_time_str, fmt_2)
        duration = (tend - tstart).total_seconds()
        return duration

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_logs = dir_info["log"]
        dir_expr = dir_info["experiment"]
        dir_setup = dir_info["setup"]
        dir_results = dir_info["result"]
        dir_output = dir_info["output"]
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
        time_latency = 0
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file):
                    self.log_output_path = dir_results + "/" + file
                    break
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            patch_space_info = (
            size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
            time_info = (time_build, time_validation, time_duration, time_latency, "")
            return patch_space_info, time_info
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        is_interrupted = False
        time_stamp_first = None
        with open(self.log_output_path, "r") as log_file:
            log_lines = log_file.readlines()
            time_stamp_start = log_lines[0].replace("\n", "")
            time_stamp_end = log_lines[-1].replace("\n", "")
            time_duration = self.time_duration(time_stamp_start, time_stamp_end)
            for line in log_lines:
                if "evaluated candidate" in line:
                    count_enumerations += 1
                elif "found plausible patch" in line:
                    count_plausible += 1
                    if time_stamp_first is None:
                        time_stamp_first = line.split(" | ")[0]
                elif "validation time: " in line:
                    time = line.split("validation time: ")[-1].strip().replace("\n", "")
                    time_validation += float(time)
                elif "build time: " in line:
                    time = line.split("build time: ")[-1].strip().replace("\n", "")
                    time_build += float(time)
                elif "possible edits" in line:
                    size_search_space = line.split(": ")[2].split(" ")[0]
                elif "plausible patches" in line:
                    count_plausible = int(line.split("found ")[-1].replace(" plausible patches", ""))
            log_file.close()
        if time_stamp_first:
            time_latency = self.compute_latency_tool(time_stamp_start, time_stamp_first)
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_interrupted:
            emitter.warning("\t\t\t\t[warning] program interrupted before starting repair")
        dir_patch = dir_results + "/patches"
        if os.path.isdir(dir_patch):
            output_patch_list = [f for f in listdir(dir_patch) if isfile(join(dir_patch, f))]
            count_generated = len(output_patch_list)
        if values.CONF_USE_VALKYRIE:
            dir_filtered = dir_results + "/patch-valid"
            count_generated = 0
            if os.path.isdir(dir_filtered):
                output_patch_list = [f for f in listdir(dir_filtered) if isfile(join(dir_filtered, f))]
                count_generated = len(output_patch_list)
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
            log_file.write("\t\t count generated patches: {0}\n".format(count_generated))
            log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
            log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time latency: {0} seconds\n".format(time_latency))
            log_file.write("\t\t time build: {0} seconds\n".format(time_build))
            log_file.write("\t\t time validation: {0} seconds\n".format(time_validation))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
        patch_space_info = (size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
        time_info = (time_build, time_validation, time_duration, time_latency, time_stamp_start)
        return patch_space_info, time_info

