import os
import shutil
import re
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter


class SenX(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(SenX, self).__init__(self.name)

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

    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        super(SenX, self).repair(dir_info, experiment_info, config_info, container_id, instrument_only)
        if not instrument_only:
            emitter.normal("\t\t\t running repair with " + self.name)
            conf_id = config_info[definitions.KEY_ID]
            dir_logs = dir_info["logs"]
            dir_setup = dir_info["setup"]
            dir_expr = dir_info["expr"]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
            additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"

            relative_binary_path = experiment_info[definitions.KEY_BINARY_PATH]
            abs_binary_path = dir_expr + "/src/" + relative_binary_path

            test_dir = dir_expr + "/tests"
            test_file_list = []
            if container_id:
                emitter.error("[Exception] unimplemented functionality: SenX docker support not implemented")
                error_exit("Unhandled Exception")
            else:
                if os.path.isdir(test_dir):
                    test_file_list = [join(test_dir, f) for f in listdir(test_dir) if isfile(join(test_dir, f))]

            if len(test_file_list) > 1:
                emitter.error("[Exception] unimplemented functionality: SenX only supports one failing test-case")
                error_exit("Unhandled Exception")
            binary_input_arg = experiment_info[definitions.KEY_CRASH_CMD]
            if "$POC" in binary_input_arg:
                binary_input_arg = binary_input_arg.replace("$POC", test_file_list[0])
            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
            execute_command(timestamp_command)
            senx_command = "timeout -k 5m {0}h senx {1}.bc ".format(str(timeout_h),abs_binary_path)
            senx_command += binary_input_arg
            senx_command += "{0} >> {1} 2>&1 ".format(additional_tool_param, self.log_output_path)
            status = execute_command(senx_command)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)

        return


    def save_logs(self, dir_results, dir_expr, dir_setup, bug_id):
        super(SenX, self).save_logs(dir_results, dir_expr, dir_setup, bug_id)
        dir_logs = "/SenX/logs/" + bug_id
        execute_command("cp -rf" + dir_logs + " " + dir_results + "/logs")

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_setup = dir_info["setup"]
        dir_results = dir_info["result"]
        bug_id = str(experiment_info[definitions.KEY_BUG_ID])
        dir_patches = "/SenX/output/" + bug_id
        if os.path.isdir(dir_patches):
            execute_command("cp -rf " + dir_patches + " " + dir_results + "/patches")
        shutil.copy(dir_setup + "/senx/instrument.sh", dir_results)
        super(SenX, self).save_artefacts(dir_info, experiment_info, container_id)
        return

    def post_process(self, dir_expr, dir_results, container_id):
        emitter.normal("\t\t\t post-processing for {}".format(self.name))
        super(SenX, self).post_process(dir_expr, dir_results, container_id)
        clean_command = "rm -rf " + dir_results + "/patches/klee-out-*"
        self.run_command(clean_command, "/dev/null", dir_expr, container_id)

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

    def pre_process(self, dir_logs, dir_expr, dir_setup, container_id):
        emitter.normal("\t\t\t pre-processing for {}".format(self.name))
        super(SenX, self).pre_process(dir_logs, dir_expr, dir_setup, container_id)

