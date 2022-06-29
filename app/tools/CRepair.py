import os
import shutil
import re
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container
from os import listdir
from os.path import isfile, join


class CRepair(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(CRepair, self).__init__(self.name)


    def generate_conf_file(self, experiment_info, conf_file_path, dir_setup):
        print(conf_file_path)
        with open(conf_file_path, "w") as conf_file:
            conf_file.write("dir_exp:{}\n".format(dir_setup))
            conf_file.write("tag_id:{}\n".format(experiment_info[definitions.KEY_BUG_ID]))
            conf_file.write("src_directory:src\n")
            conf_file.write("binary_path:{}\n".format(experiment_info[definitions.KEY_BINARY_PATH]))
            conf_file.write("config_command:{}\n".format(dir_setup + "/config.sh /experiment"))
            conf_file.write("build_command:{}\n".format(dir_setup + "/build.sh /experiment"))
            conf_file.write("test_input_list:{}\n".format(experiment_info[definitions.KEY_CRASH_CMD]))
            conf_file.write("poc_list:{}\n".format(",".join(experiment_info[definitions.KEY_EXPLOIT_LIST])))


    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id, container_id, source_file):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        instrumentation_script_path = "{0}/{1}/instrument.sh".format(dir_setup, self.name.lower())

        if container_id:
            instrumentation_exist = container.is_file(container_id, instrumentation_script_path)
        else:
            instrumentation_exist = os.path.isfile(instrumentation_script_path)
        if instrumentation_exist:
            command_str = "bash instrument.sh {}".format(dir_expr)
            dir_setup_exp = dir_setup + "/{}".format(self.name.lower())
            status = self.run_command(command_str, self.log_instrument_path, dir_setup_exp, container_id)
            if not status == 0:
                error_exit("error with instrumentation of ", self.name)
        return

    def prepare(self, dir_logs, dir_expr, dir_setup, bug_id, container_id, experiment_info):
        """preparation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t preparing for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        if container_id:
            tmp_repair_file = "/tmp/repair.conf"
            repair_conf_path = dir_expr + "/src/repair.conf"
            self.generate_conf_file(experiment_info, tmp_repair_file, dir_setup)
            save_command = "docker cp " + tmp_repair_file + " " + container_id + ":" + repair_conf_path
            execute_command(save_command)

        else:
            repair_conf_path = dir_expr + "/src/repair.conf"
            self.generate_conf_file(experiment_info, repair_conf_path, dir_setup)
        return repair_conf_path


    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        if not instrument_only:
            emitter.normal("\t\t\t running repair with " + self.name)
            conf_id = config_info[definitions.KEY_ID]
            dir_logs = dir_info["logs"]
            dir_setup = dir_info["setup"]
            dir_expr = dir_info["expr"]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
            additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
            repair_conf_path = self.prepare(dir_logs, dir_expr, dir_setup, bug_id, container_id, experiment_info)
            self.instrument(dir_logs, dir_expr, dir_setup, bug_id, container_id, experiment_info)
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
            relative_binary_path = experiment_info[definitions.KEY_BINARY_PATH]
            abs_binary_path = dir_expr + "/src/" + relative_binary_path
            binary_dir_path = "/".join(abs_binary_path.split("/")[:-1])
            struct_def_file_path = "def_file"
            test_dir = dir_setup + "/tests"

            timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
            execute_command(timestamp_command)
            CRepair_command = "cd {};".format(binary_dir_path)
            CRepair_command += "timeout -k 5m {0}h crepair --conf={1} ".format(str(timeout_h),
                                                                              repair_conf_path)
            CRepair_command += "{0} >> {1} 2>&1 ".format(additional_tool_param, self.log_output_path)
            status = execute_command(CRepair_command)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
            timestamp_command = "printf \"\\n\" >> " + self.log_output_path
            timestamp_command += ";echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)

        return

    def save_logs(self, dir_results, dir_expr, dir_setup, bug_id):
        super(CRepair, self).save_logs(dir_results, dir_expr, dir_setup, bug_id)
        dir_logs = "/CRepair/logs/" + bug_id
        execute_command("cp -rf" + dir_logs + " " + dir_results + "/logs")

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_exp = dir_info["experiment"]
        dir_output = dir_info["output"]
        bug_id = str(experiment_info[definitions.KEY_BUG_ID])
        copy_command = "cp -rf " + dir_exp + "/CRepair " + dir_output
        execute_command(copy_command)
        relative_binary_path = experiment_info[definitions.KEY_BINARY_PATH]
        abs_binary_path = dir_exp + "/src/" + relative_binary_path
        patch_path = abs_binary_path + ".bc.patch"
        copy_command = "cp -rf " + patch_path + " " + dir_output + "/patches"
        execute_command(copy_command)
        super(CRepair, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def post_process(self, dir_expr, dir_results, container_id):
        emitter.normal("\t\t\t post-processing for {}".format(self.name))
        super(CRepair, self).post_process(dir_expr, dir_results, container_id)

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_logs = dir_info["log"]
        dir_expr = dir_info["experiment"]
        dir_setup = dir_info["setup"]
        dir_results = dir_info["result"]
        dir_output = dir_info["output"]
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
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
        is_error = False

        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r", encoding="iso-8859-1") as log_file:
                log_lines = log_file.readlines()
                time_start = log_lines[0].replace("\n", "")
                time_end = log_lines[-1].replace("\n", "")
                time_duration = self.time_duration(time_start, time_end)
                for line in log_lines:
                    if "Creating patch" in line:
                        count_plausible = 1
                        count_enumerations = 1
                    elif "Runtime Error" in line:
                        is_error = True
                log_file.close()
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")

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
        patch_space_info = (size_search_space, count_enumerations, count_plausible, count_non_compilable, count_generated)
        time_info = (time_build, time_validation, time_duration, time_latency, time_first)
        return patch_space_info, time_info

    def pre_process(self, dir_logs, dir_expr, dir_setup, container_id):
        emitter.normal("\t\t\t pre-processing for {}".format(self.name))
        super(CRepair, self).pre_process(dir_logs, dir_expr, dir_setup, container_id)

