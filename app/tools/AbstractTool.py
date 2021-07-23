import abc
import os
import shutil
from app.utilities import execute_command, error_exit, values


class AbstractTool:
    log_instrument_path = None
    log_output_path = None
    name = None

    def __init__(self):
        pass

    def instrument(self, dir_logs, dir_expr, dir_setup, bug_id):
        """instrumentation for the experiment as needed by the tool"""
        print("\t[INFO] instrumenting for", self.name)
        self.log_instrument_path = dir_logs + "/" + self.name + "-" + bug_id + "-instrument.log"
        if os.path.isfile(dir_expr + "{}/instrument.sh".format(self.name.lower())):
            if not os.path.isfile(dir_expr + "/src/INSTRUMENTED"):
                command_str = "cd " + dir_expr + "/{}; bash instrument.sh;".format(self.name.lower())
                command_str += " > {0} 2>&1".format(self.log_instrument_path)
                status = execute_command(command_str)
                if not status == 0:
                    error_exit("error with instrumentation of ", self.name)
                with open(dir_expr + "/src/INSTRUMENTED", 'w') as fp:
                    pass
        else:
            error_exit("no instrumentation available for ", self.name)
        return

    @abc.abstractmethod
    def repair(self, dir_logs, dir_expr, dir_setup, bug_id, timeout, passing_test_list,
               failing_test_list, fix_location, subject_name, binary_path, additional_tool_param, binary_input_arg):
        """invoking the tool for the repair process"""
        return

    def pre_process(self):
        """any pre-processing required for the repair"""
        print("\t[INFO] check for {}".format(self.name))
        check_command = "{} --help".format(self.name.lower())
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
    def save_artefacts(self, dir_results, dir_expr, dir_setup, bug_id):
        """store all artefacts from the tool"""
        return

    def save_logs(self, dir_results, dir_setup, bug_id):
        if os.path.isfile(self.log_instrument_path):
            shutil.copy(self.log_instrument_path, dir_results)
        if os.path.isfile(self.log_output_path):
            shutil.copy(self.log_output_path, dir_results)
        return

    def clean_up(self, exp_dir):
        if os.path.isdir(exp_dir):
            rm_command = "rm -rf " + exp_dir
            execute_command(rm_command)

