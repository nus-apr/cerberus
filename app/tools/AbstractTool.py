import abc
import os
from app.utilities import execute_command, error_exit
from app import emitter, values, container, utilities, definitions
from datetime import datetime


class AbstractTool:
    log_instrument_path = None
    log_output_path = None
    name = None
    dir_logs = ""
    dir_output = ""
    dir_expr = ""
    dir_inst = ""
    dir_setup = ""
    container_id = None
    is_instrument_only = False


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


    def clean_up(self):
        if self.container_id:
            container.remove_container(self.container_id)
        else:
            if os.path.isdir(self.dir_exp):
                rm_command = "rm -rf " + self.dir_exp
                execute_command(rm_command)

    def update_info(self, container_id, instrument_only, dir_info):
        self.container_id = container_id
        self.is_instrument_only = instrument_only
        self.update_dir_info(dir_info)



    def update_dir_info(self, dir_info):
        if self.container_id:
            self.dir_expr = dir_info["container"]["experiment"]
            self.dir_logs = dir_info["container"]["logs"]
            self.dir_inst = dir_info["container"]["instrumentation"]
            self.dir_setup = dir_info["container"]["setup"]
        else:
            self.dir_expr = dir_info["local"]["experiment"]
            self.dir_logs = dir_info["local"]["logs"]
            self.dir_inst = dir_info["local"]["instrumentation"]
            self.dir_setup = dir_info["local"]["setup"]


    def run_command(self, command_str, log_file_path, dir_path):
        """executes the specified command at the given dir_path and save the output to log_file"""
        if self.container_id:
            exit_code, output = container.exec_command(self.container_id, command_str, dir_path)
            stdout, stderr = output
            if "/dev/null" not in log_file_path:
                with open(log_file_path, 'a') as log_file:
                    if stdout:
                        log_file.writelines(stdout.decode("iso-8859-1"))
                    if stderr:
                        log_file.writelines(stderr.decode("iso-8859-1"))
        else:
            command_str = "cd " + dir_path + ";" + command_str
            command_str += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command_str)
        return exit_code


    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.CONFIG_ID)
        self.log_instrument_path = self.dir_logs + "/" + conf_id + "-" + self.name + "-" + bug_id + "-instrument.log"
        command_str = "bash instrument.sh {} > {} 2>&1".format(self.dir_expr, self.log_instrument_path)
        status = self.run_command(command_str, "/dev/null", self.dir_inst)
        if status not in [0, 126]:
            error_exit("error with instrumentation of " + self.name + "; exit code " + str(status))
        return


    @abc.abstractmethod
    def repair(self, bug_info, config_info):
        emitter.normal("\t\t[repair-tool] repairing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        log_file_name = conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
        self.log_output_path = os.path.join(self.dir_logs,log_file_name)
        return


    def pre_process(self):
        """any pre-processing required for the repair"""
        self.check_tool_exists()
        if self.container_id:
            clean_command = "rm -rf /output/patch* /logs"
            self.run_command(clean_command, "/dev/null", "/")
            script_path = definitions.DIR_SCRIPTS + "/{}-dump-patches.py".format(self.name)
            cp_script_command = "docker cp {} {}:{} ".format(script_path, self.container_id,
                                                             self.dir_expr)
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

    def post_process(self):
        """any post-processing required for the repair"""
        if self.container_id:
            container.stop_container(self.container_id)
        if values.CONF_PURGE:
            self.clean_up()
        return

    @abc.abstractmethod
    def save_artefacts(self, dir_info, experiment_info, container_id):
        """store all artefacts from the tool"""
        dir_results = dir_info["result"]
        dir_output = dir_info["output"]
        dir_logs = dir_info["log"]
        save_command = "cp -rf " + self.dir_output + "/* " + dir_results + ";"
        save_command += "cp -rf " + dir_logs + "/* " + dir_results
        execute_command(save_command)
        return

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """analyse tool output and collect information"""
        return


    def print_analysis(self, space_info, time_info):
        size_space, n_enumerated, n_plausible, n_noncompile, n_generated = space_info
        time_build, time_validation, time_duration, latency_1, latency_2, latency_3, _ = time_info
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
        emitter.highlight("\t\t\t time latency compilation: {0} seconds".format(latency_3))
        emitter.highlight("\t\t\t time latency validation: {0} seconds".format(latency_2))
        emitter.highlight("\t\t\t time latency plausible: {0} seconds".format(latency_1))


    def append_file(self, content, file_path):
        if self.container_id:
            container.write_file(file_path, content, self.container_id)
        else:
            with open(file_path, "w") as f:
                for line in content:
                    f.write(line)


    def write_file(self, content, file_path):
        if self.container_id:
            container.write_file(file_path, content, self.container_id)
        else:
            with open(file_path, "a") as f:
                for line in content:
                    f.write(line)


    def list_dir(self, dir_path):
        file_list = []
        if self.container_id:
            if container.is_dir(self.container_id, dir_path):
                list_files = container.list_dir(self.container_id, dir_path)
                file_list = [ os.path.join(dir_path, t) for t in list_files]
        else:
            if os.path.isdir(dir_path):
                list_files = os.listdir(dir_path)
                file_list = [ os.path.join(dir_path, t) for t in list_files]
        return file_list

    def is_dir(self, dir_path):
        if self.container_id:
            if container.is_dir(self.container_id, dir_path):
                return True
        else:
            if os.path.isdir(dir_path):
                return True
        return False
