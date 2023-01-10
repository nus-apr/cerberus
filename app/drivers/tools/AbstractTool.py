import abc
from datetime import datetime
import os
from os.path import join
import re
from app.core.utilities import execute_command, error_exit
from app.core import (
    emitter,
    values,
    container,
    definitions,
    abstractions,
    analysis,
)
from app.core import utilities


class AbstractTool:
    log_instrument_path = None
    log_output_path = None
    image_name = None
    invoke_command = None
    name = None
    dir_logs = ""
    dir_output = ""
    dir_expr = ""
    dir_base_expr = ""
    dir_inst = ""
    dir_setup = ""
    container_id = None
    is_instrument_only = False
    timestamp_fmt = "%a %d %b %Y %H:%M:%S %p"
    _time = analysis.TimeAnalysis()
    _space = analysis.SpaceAnalysis()
    _error = analysis.ErrorAnalysis()

    def __init__(self, tool_name):
        """add initialization commands to all tools here"""
        emitter.debug("using tool: " + tool_name)
        self.image_name = "cerberus:{}".format(tool_name.lower())

    @abc.abstractmethod
    def analyse_output(self, dir_info, bug_id, fail_list):
        """analyse tool output and collect information"""
        return self._space, self._time, self._error

    def clean_up(self):
        if self.container_id:
            container.remove_container(self.container_id)
        else:
            if os.path.isdir(self.dir_expr):
                rm_command = "rm -rf " + self.dir_expr
                execute_command(rm_command)

    def update_info(self, container_id, instrument_only, dir_info):
        self.container_id = container_id
        self.is_instrument_only = instrument_only
        self.update_dir_info(dir_info)
        self._time = analysis.TimeAnalysis()
        self._space = analysis.SpaceAnalysis()
        self._error = analysis.ErrorAnalysis()

    def update_dir_info(self, dir_info):
        if self.container_id:
            self.dir_expr = dir_info["container"]["experiment"]
            self.dir_logs = dir_info["container"]["logs"]
            self.dir_inst = dir_info["container"]["instrumentation"]
            self.dir_setup = dir_info["container"]["setup"]
            self.dir_output = dir_info["container"]["artifacts"]
            self.dir_base_expr = "/experiment"
        else:
            self.dir_expr = dir_info["local"]["experiment"]
            self.dir_logs = dir_info["local"]["logs"]
            self.dir_inst = dir_info["local"]["instrumentation"]
            self.dir_setup = dir_info["local"]["setup"]
            self.dir_output = dir_info["local"]["artifacts"]
            self.dir_base_expr = definitions.DIR_EXPERIMENT

    def timestamp_log(self):
        timestamp_command = "date -u '+%a %d %b %Y %H:%M:%S %p'"
        self.run_command(timestamp_command, self.log_output_path)

    def run_command(
        self, command_str, log_file_path="/dev/null", dir_path="/experiment", env=None
    ):
        """executes the specified command at the given dir_path and save the output to log_file"""
        if self.container_id:
            exit_code, output = container.exec_command(
                self.container_id, command_str, dir_path, env
            )
            stdout, stderr = output
            if "/dev/null" not in log_file_path:
                if stdout:
                    self.append_file(stdout.decode("iso-8859-1"), log_file_path)
                if stderr:
                    self.append_file(stderr.decode("iso-8859-1"), log_file_path)
        else:
            command_str = "cd " + dir_path + ";" + command_str
            command_str += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command_str, env=env)
        return exit_code

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.CONFIG_ID)
        buggy_file = bug_info[definitions.KEY_FIX_FILE]
        self.log_instrument_path = join(
            self.dir_logs, "{}-{}-{}-instrument.log".format(conf_id, self.name, bug_id)
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        emitter.normal(
            "\t\t\t Instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of {}; exit code {}".format(
                    self.name, str(status)
                )
            )
        return

    def repair(self, bug_info, config_info):
        emitter.normal("\t\t[repair-tool] repairing experiment subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        log_file_name = "{}-{}-{}-output.log".format(
            conf_id, self.name.lower(), bug_id, "-output.log"
        )
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return

    def pre_process(self):
        """Any pre-processing required for the repair"""
        self.check_tool_exists()
        if self.container_id:
            clean_command = "rm -rf /output/patch* /logs/*"
            self.run_command(clean_command, "/dev/null", "/")
            script_path = definitions.DIR_SCRIPTS + "/{}-dump-patches.py".format(
                self.name
            )
            cp_script_command = "docker cp {} {}:{} ".format(
                script_path, self.container_id, self.dir_expr
            )
            execute_command(cp_script_command)
        return

    def check_tool_exists(self):
        """Any pre-processing required for the repair"""
        if values.DEFAULT_USE_CONTAINER:
            if self.image_name is None:
                utilities.error_exit(
                    "{} does not provide a Docker Image".format(self.name)
                )
            if ":" in self.image_name:
                repo_name, tag_name = self.image_name.split(":")
            else:
                repo_name = self.image_name
                tag_name = "latest"
            if not container.is_image_exist(repo_name, tag_name):
                emitter.warning("[warning] docker image not found in Docker registry")
                if container.pull_image(repo_name, tag_name) is None:
                    utilities.error_exit(
                        "{} does not provide a Docker image in Dockerhub".format(
                            self.name
                        )
                    )
                    # container.build_tool_image(repo_name, tag_name)
        else:
            check_command = "which {}".format(self.name.lower())
            emitter.information(check_command)
            ret_code = execute_command(check_command)
            if int(ret_code) != 0:
                error_exit("{} not Found".format(self.name))
        return

    def post_process(self):
        """Any post-processing required for the repair"""
        if self.container_id:
            container.stop_container(self.container_id)
        if values.CONF_PURGE:
            self.clean_up()
        return

    def save_artefacts(self, dir_info):
        """Store all artefacts from the tool"""
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_results = dir_info["results"]
        dir_artefacts = dir_info["artifacts"]
        dir_logs = dir_info["logs"]
        if self.container_id:
            container.copy_file_from_container(
                self.container_id, self.dir_output, dir_results
            )
            container.copy_file_from_container(
                self.container_id, self.dir_logs, dir_results
            )
            container.copy_file_from_container(
                self.container_id, self.dir_output, dir_artefacts
            )
            container.copy_file_from_container(
                self.container_id, self.dir_logs, dir_logs
            )
            pass
        else:
            save_command = "cp -rf {}/* {};".format(self.dir_output, dir_results)
            if self.dir_logs != "":
                save_command += "cp -rf {}/* {};".format(self.dir_logs, dir_results)
            if dir_artefacts != "":
                save_command += "cp -rf {}/* {};".format(self.dir_output, dir_artefacts)
            if dir_logs != "":
                save_command += "cp -rf {}/*".format(self.dir_logs, dir_logs)

            execute_command(save_command)
        return

    def print_analysis(
        self, space_info: analysis.SpaceAnalysis, time_info: analysis.TimeAnalysis
    ):
        emitter.highlight("\t\t\t search space size: {0}".format(space_info.size))
        emitter.highlight(
            "\t\t\t count enumerations: {0}".format(space_info.enumerations)
        )
        emitter.highlight(
            "\t\t\t count plausible patches: {0}".format(space_info.plausible)
        )
        emitter.highlight("\t\t\t count generated: {0}".format(space_info.generated))
        emitter.highlight(
            "\t\t\t count non-compiling patches: {0}".format(space_info.non_compilable)
        )
        emitter.highlight(
            "\t\t\t count implausible patches: {0}".format(space_info.get_implausible())
        )
        emitter.highlight(
            "\t\t\t time build: {0} seconds".format(time_info.total_build)
        )
        emitter.highlight(
            "\t\t\t time validation: {0} seconds".format(time_info.total_validation)
        )
        emitter.highlight(
            "\t\t\t time duration: {0} seconds".format(time_info.get_duration())
        )
        emitter.highlight(
            "\t\t\t time latency compilation: {0} seconds".format(
                time_info.get_latency_compilation()
            )
        )
        emitter.highlight(
            "\t\t\t time latency validation: {0} seconds".format(
                time_info.get_latency_validation()
            )
        )
        emitter.highlight(
            "\t\t\t time latency plausible: {0} seconds".format(
                time_info.get_latency_plausible()
            )
        )

    def read_file(self, file_path, encoding="utf-8"):
        return abstractions.read_file(self.container_id, file_path, encoding)

    def append_file(self, content, file_path):
        return abstractions.append_file(self.container_id, content, file_path)

    def write_file(self, content, file_path):
        return abstractions.write_file(self.container_id, content, file_path)

    def list_dir(self, dir_path):
        return abstractions.list_dir(self.container_id, dir_path)

    def is_dir(self, dir_path):
        return abstractions.is_dir(self.container_id, dir_path)

    def is_file(self, file_path):
        return abstractions.is_file(self.container_id, file_path)

    def get_time_analysis(self):
        return self._time

    def get_output_log_path(self):
        # parse this file for time info
        if not self.log_output_path:
            regex = re.compile("(.*-output.log$)")
            for _, _, files in os.walk(self.dir_logs):
                for file in files:
                    if regex.match(file) and self.name in file:
                        self.log_output_path = os.path.join(self.dir_logs, file)
                        break
        return self.log_output_path
