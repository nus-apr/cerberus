import abc
import os
import shutil
from app.utilities import execute_command, error_exit
from app import emitter, values, container, utilities, definitions
from datetime import datetime

class AbstractTool:
    log_instrument_path = None
    log_output_path = None
    name = None

    def __init__(self, tool_name):
        """add initialization commands to all tools here"""
        emitter.debug("using tool: " + tool_name)

    def time_duration(self, start_time_str, end_time_str):
        # Fri 08 Oct 2021 04:59:55 PM +08
        fmt = '%a %d %b %Y %H:%M:%S %p'
        start_time_str = start_time_str.split(" +")[0].strip()
        end_time_str = end_time_str.split(" +")[0].strip()
        tstart = datetime.strptime(start_time_str, fmt)
        tend = datetime.strptime(end_time_str, fmt)
        duration = (tend - tstart).total_seconds()
        return duration

    def run_command(self, command_str, log_file_path, exp_dir_path, container_id):
        if container_id:
            exit_code, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            if "/dev/null" not in log_file_path:
                with open(log_file_path, 'a') as log_file:
                    if stdout:
                        log_file.writelines(stdout.decode("iso-8859-1"))
                    if stderr:
                        log_file.writelines(stderr.decode("iso-8859-1"))
        else:
            command_str = "cd " + exp_dir_path + ";" + command_str
            command_str += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command_str)
        return exit_code

    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id, container_id, source_file):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        command_str = "bash instrument.sh".format(source_file)
        dir_setup_exp = dir_setup + "/{}".format(self.name.lower())
        status = self.run_command(command_str, self.log_instrument_path, dir_setup_exp, container_id)
        if status not in [0, 126]:
            error_exit("error with instrumentation of " + self.name + "; exit code " + str(status))
        return

    @abc.abstractmethod
    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        emitter.normal("\t\t[repair-tool] repairing experiment subject")
        utilities.check_space()
        self.pre_process(dir_info['logs'], dir_info['expr'], dir_info['setup'], container_id)
        self.instrument(dir_info['logs'], dir_info['expr'],
                        dir_info['setup'], experiment_info['bug_id'],
                        container_id, experiment_info['source_file'])
        return

    def pre_process(self, dir_logs, dir_expr, dir_setup, container_id):
        """any pre-processing required for the repair"""
        self.check_tool_exists()
        if container_id:
            clean_command = "rm -rf /output/patch* /logs"
            self.run_command(clean_command, "/dev/null", "/", container_id)
            script_path = definitions.DIR_SCRIPTS + "/{}-dump-patches.py".format(self.name)
            cp_script_command = "docker cp {} {}:{} ".format(script_path, container_id, dir_expr)
            execute_command(cp_script_command)
        return

    def check_tool_exists(self):
        """any pre-processing required for the repair"""
        if values.DEFAULT_USE_CONTAINER:
            if not container.check_image_exist(self.name.lower()):
                emitter.warning("[warning] docker image not found")
                if container.pull_image(self.name.lower()) is None:
                    container.build_tool_image(self.name.lower())
        else:
            check_command = "which {}".format(self.name.lower())
            ret_code = execute_command(check_command)
            if int(ret_code) != 0:
                error_exit("{} not Found".format(self.name))
        return

    def post_process(self, dir_expr, dir_results, container_id):
        """any post-processing required for the repair"""
        if container_id:
            container.stop_container(container_id)
        if values.CONF_PURGE:
            self.clean_up(dir_expr, container_id)
        return

    @abc.abstractmethod
    def save_artefacts(self, dir_info, experiment_info, container_id):
        """store all artefacts from the tool"""
        dir_results = dir_info["result"]
        dir_output = dir_info["output"]
        dir_logs = dir_info["log"]
        save_command = "cp -rf " + dir_output + "/* " + dir_results + ";"
        save_command += "cp -rf " + dir_logs + "/* " + dir_results
        execute_command(save_command)
        return

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """analyse tool output and collect information"""
        return

    def print_analysis(self, space_info, time_info):
        size_space, n_enumerated, n_plausible, n_noncompile, n_generated = space_info
        time_build, time_validation, time_duration, latency_1, latency_2, _ = time_info
        n_implausible = n_enumerated - n_plausible - n_noncompile
        emitter.highlight("\t\t\t search space size: {0}".format(size_space))
        emitter.highlight("\t\t\t count enumerations: {0}".format(n_enumerated))
        emitter.highlight("\t\t\t count plausible patches: {0}".format(n_plausible))
        emitter.highlight("\t\t\t count generated: {0}".format(n_generated))
        emitter.highlight("\t\t\t count non-compiling patches: {0}".format(n_noncompile))
        emitter.highlight("\t\t\t count implausible patches: {0}".format(n_implausible))
        emitter.highlight("\t\t\t time build: {0} seconds".format(time_build))
        emitter.highlight("\t\t\t time validation: {0} seconds".format(time_validation))
        emitter.highlight("\t\t\t time duration: {0} seconds".format(time_duration))
        emitter.highlight("\t\t\t time latency validation: {0} seconds".format(latency_2))
        emitter.highlight("\t\t\t time latency plausible: {0} seconds".format(latency_1))

    def clean_up(self, exp_dir, container_id):
        if container_id:
            container.remove_container(container_id)
        else:
            if os.path.isdir(exp_dir):
                rm_command = "rm -rf " + exp_dir
                execute_command(rm_command)

