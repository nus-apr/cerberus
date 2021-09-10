import abc
import os
import shutil
from app.utilities import execute_command, error_exit
from app import emitter, values, container


class AbstractTool:
    log_instrument_path = None
    log_output_path = None
    name = None

    def __init__(self, tool_name):
        """add initialization commands to all tools here"""
        emitter.debug("using tool: " + tool_name)

    def run_command(self, command_str, log_file_path, container_id=None, exp_dir_path="/experiment"):
        if container_id:
            exit_code, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            if log_file_path:
                with open(log_file_path, 'w') as log_file:
                    if stdout:
                        log_file.writelines(stdout.decode("utf-8"))
                    if stderr:
                        log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str += " > {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command_str)
        return exit_code


    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id, container_id):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        if os.path.isfile(dir_setup + "/{}/instrument.sh".format(self.name.lower())):
            if not os.path.isfile(dir_setup + "/src/INSTRUMENTED"):
                command_str = "cd " + dir_setup + "/{}; bash instrument.sh ".format(self.name.lower())
                command_str += " > {0} 2>&1".format(self.log_instrument_path)
                status = execute_command(command_str)
                if not status == 0:
                    error_exit("error with instrumentation of ", self.name)
                with open(dir_expr + "/src/INSTRUMENTED", 'w') as fp:
                    pass
        else:
            emitter.warning("\t[warning] no instrumentation available for " + self.name)
        return

    @abc.abstractmethod
    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg, container_id):
        """invoking the tool for the repair process"""
        return

    def pre_process(self, dir_logs, dir_expr, dir_setup, container_id):
        """any pre-processing required for the repair"""
        self.check_tool_exists()
        return

    def check_tool_exists(self):
        """any pre-processing required for the repair"""
        if values.CONF_USE_CONTAINER:
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

    def post_process(self, dir_expr, dir_results):
        """any post-processing required for the repair"""
        if values.CONF_PURGE:
            self.clean_up(dir_expr)
        return

    @abc.abstractmethod
    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id, container_id):
        """store all artefacts from the tool"""
        return

    @abc.abstractmethod
    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        """analyse tool output and collect information"""
        return

    def print_analysis(self, size_space, n_enumerated, n_plausible, n_noncompile):
        n_implausible = n_enumerated - n_plausible - n_noncompile
        emitter.highlight("\t\t\t search space size: {0}".format(size_space))
        emitter.highlight("\t\t\t count enumerations: {0}".format(n_enumerated))
        emitter.highlight("\t\t\t count plausible patches: {0}".format(n_plausible))
        emitter.highlight("\t\t\t count non-compiling patches: {0}".format(n_noncompile))
        emitter.highlight("\t\t\t count implausible patches: {0}".format(n_implausible))

    def save_logs(self, dir_results, dir_expr, dir_setup, bug_id, container_id):
        if os.path.isfile(self.log_instrument_path):
            shutil.move(self.log_instrument_path, dir_results)
        if os.path.isfile(self.log_output_path):
            shutil.move(self.log_output_path, dir_results)
        return

    def clean_up(self, exp_dir):
        if os.path.isdir(exp_dir):
            rm_command = "rm -rf " + exp_dir
            execute_command(rm_command)

