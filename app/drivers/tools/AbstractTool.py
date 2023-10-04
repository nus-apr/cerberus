import abc
import os
import re
import shutil
import time
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core import abstractions
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.task.stats import ToolStats
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.core.utilities import execute_command
from app.drivers.AbstractDriver import AbstractDriver
from app.ui import ui


class AbstractTool(AbstractDriver):
    log_instrument_path = ""
    log_output_path = ""
    image_name = ""
    invoke_command = ""
    name = ""
    dir_logs = ""
    dir_output = ""
    dir_expr = ""
    dir_base_expr = ""
    cpu_usage = 1
    gpu_usage = 0
    dir_inst = ""
    dir_setup = ""
    hash_digest = ""
    container_id: Optional[str] = None
    is_instrument_only = False
    timestamp_fmt = "%a %d %b %Y %H:%M:%S %p"
    current_task_profile_id = values.current_task_profile_id
    key_benchmark = definitions.KEY_BENCHMARK
    key_subject = definitions.KEY_SUBJECT
    key_language = definitions.KEY_LANGUAGE
    key_id = definitions.KEY_ID
    key_bug_id = definitions.KEY_BUG_ID
    key_bug_type = definitions.KEY_BUG_TYPE
    key_tool_params = definitions.KEY_TOOL_PARAMS
    key_timeout = definitions.KEY_CONFIG_TIMEOUT
    key_source = definitions.KEY_SOURCE
    key_sink = definitions.KEY_SINK
    key_compile_programs = definitions.KEY_COMPILE_PROGRAMS
    key_build_command = definitions.KEY_BUILD_COMMAND
    key_config_command = definitions.KEY_CONFIG_COMMAND
    key_build_script = definitions.KEY_BUILD_SCRIPT
    key_config_script = definitions.KEY_CONFIG_SCRIPT
    key_test_script = definitions.KEY_TEST_SCRIPT
    key_gpus = definitions.KEY_GPUS
    key_cpus = definitions.KEY_CPUS
    stats: ToolStats
    bindings: Optional[Dict[str, Any]] = None

    def __init__(self, tool_name: str):
        """add initialization commands to all tools here"""
        super().__init__()
        self.name = tool_name
        if not self.stats:
            self.error_exit("Stats should be set in the abstract tool constructor!")
        self.is_ui_active = values.ui_active
        self.is_only_instrument = values.only_instrument
        self.is_debug = values.debug
        self.is_dump_patches = values.dump_patches
        self.use_container = values.use_container
        self.use_valkyrie = values.use_valkyrie
        self.use_gpu = super().get_config_value("use_gpu")

    @abc.abstractmethod
    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> ToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """
        return self.stats

    def clean_up(self) -> None:
        if self.container_id:
            container.remove_container(self.container_id)
        else:
            if os.path.isdir(self.dir_expr):
                rm_command = "rm -rf {}".format(self.dir_expr)
                execute_command(rm_command)

    def update_info(
        self,
        container_id: Optional[str],
        instrument_only: bool,
        dir_info: DirectoryInfo,
    ) -> None:
        self.container_id = container_id
        self.is_instrument_only = instrument_only
        self.update_dir_info(dir_info)

    def update_container_stats(self, container_id: str) -> None:
        container_stats = container.get_container_stats(container_id)
        self.stats.container_stats.load_container_stats(container_stats)

    def update_dir_info(self, dir_info: DirectoryInfo):
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
            self.dir_base_expr = values.dir_experiments

    def timestamp_log(self):
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"{time_now}"
        self.append_file(timestamp_txt, self.log_output_path)

    def timestamp_log_start(self):
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"{time_now}\n"
        self.append_file(timestamp_txt, self.log_output_path)

    def timestamp_log_end(self):
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"\n{time_now}"
        self.append_file(timestamp_txt, self.log_output_path)

    def run_command(
        self, command: str, log_file_path="/dev/null", dir_path=None, env=dict()
    ):
        """executes the specified command at the given dir_path and save the output to log_file without returning the result"""
        if self.container_id:
            if not dir_path:
                dir_path = "/experiment"
            exit_code, output = container.exec_command(
                self.container_id, command, dir_path, env
            )
            if output:
                stdout, stderr = output
                if "/dev/null" not in log_file_path:
                    if stdout:
                        self.append_file(stdout.decode("iso-8859-1"), log_file_path)
                    if stderr:
                        self.append_file(stderr.decode("iso-8859-1"), log_file_path)
        else:
            if not dir_path:
                dir_path = self.dir_expr
            command += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command, env=env, directory=dir_path)
        return exit_code

    def exec_command(
        self, command: str, log_file_path="/dev/null", dir_path=None, env=dict()
    ):
        """executes the specified command at the given dir_path and save the output to log_file"""
        if self.container_id:
            if not dir_path:
                dir_path = "/experiment"
            exit_code, output = container.exec_command(
                self.container_id, command, dir_path, env
            )
            if output:
                stdout, stderr = output
                if "/dev/null" not in log_file_path:
                    if stdout:
                        self.append_file(stdout.decode("iso-8859-1"), log_file_path)
                    if stderr:
                        self.append_file(stderr.decode("iso-8859-1"), log_file_path)
            return exit_code, output
        else:
            if not dir_path:
                dir_path = self.dir_expr
            command += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command, env=env, directory=dir_path)
        return exit_code, None

    def process_status(self, status: int) -> None:
        """Process the status of running a command"""
        if status != 0:
            self.stats.error_stats.is_error = True
            values.experiment_status.set(TaskStatus.FAIL_IN_TOOL)
            emitter.warning(
                "\t\t\t[framework] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
            if (status == 137 or status == 124) and self.container_id:
                # Due to the container being killed, we restart it to be able to pull out the analysis info
                container.stop_container(self.container_id)
                container.start_container(self.container_id)

        else:
            values.experiment_status.set(TaskStatus.SUCCESS)
            emitter.success(
                "\t\t\t[framework] {0} ended successfully".format(self.name)
            )

    def pre_process(self) -> None:
        """Any pre-processing required for the repair"""
        # self.check_tool_exists()
        return

    def check_tool_exists(self) -> None:
        """Check that the tool is available either as an image or locally"""
        if values.use_container:
            if not self.hash_digest.startswith("sha256:"):
                self.hash_digest = "sha256:" + self.hash_digest
            if self.image_name is None:
                utilities.error_exit(
                    "\t[framework] {} does not provide a Docker Image".format(self.name)
                )
            if ":" in self.image_name:
                repo_name, tag_name = self.image_name.split(":")
            else:
                repo_name = self.image_name
                tag_name = "latest"
            if not container.image_exists(repo_name, tag_name):
                emitter.warning(
                    "\t[framework] docker image {}:{} not found in local docker registry".format(
                        repo_name, tag_name
                    )
                )
                image = container.pull_image(repo_name, tag_name)
                if image is None:
                    utilities.error_exit(
                        "\t[framework] {} does not provide a Docker image {}:{} in Dockerhub".format(
                            self.name, repo_name, tag_name
                        )
                    )
                if values.secure_hash and not image.id.startswith(self.hash_digest):
                    utilities.error_exit(
                        "\t[framework] pulled an image for {} whose hash did start with the prefix in the driver. aborting".format(
                            self.name
                        )
                    )
                    # container.build_tool_image(repo_name, tag_name)
            else:
                # Image may exist but need to be sure it is the latest one
                emitter.information(
                    "\t\t[framework] docker image {}:{} found locally for {}".format(
                        repo_name, tag_name, self.name
                    )
                )
                # Get the local image
                local_image = container.get_image(repo_name, tag_name)
                # Then try pulling. If it is the same one we are quick
                # If not we have to wait but it is safer than getting stale results.
                # In theory this has a supply chain vulnerability but we can assume
                # That the storage is safe
                if values.use_latest_image:
                    remote_image = container.pull_image(repo_name, tag_name)

                    if remote_image and local_image.id != remote_image.id:  # type: ignore
                        emitter.information(
                            "\t[framework] docker image {}:{} is not the same as the one in the repository. Will have to rebuild".format(
                                repo_name, tag_name
                            )
                        )
                        if values.secure_hash and not remote_image.id.startswith(
                            self.hash_digest
                        ):
                            utilities.error_exit(
                                "\t[framework] secure mode is enabled. aborting"
                            )
                        values.rebuild_all = True

        else:
            local_path = shutil.which(self.name.lower())
            if not local_path:
                error_exit("{} not Found".format(self.name))
        return

    def update_experiment_status(self, status: str) -> None:
        """Update the status of the experiment if any visualization is available"""
        ui.update_current_job(status)

    def post_process(self) -> None:
        """Any post-processing required for the repair"""
        if self.container_id:
            container.stop_container(self.container_id)
        if values.use_purge:
            self.clean_up()
        return

    def print_stats(self) -> None:
        """Print the statistics of the tool."""
        pass

    def save_artifacts(self, dir_info: Dict[str, str]):
        """Store all artifacts from the tool"""
        dir_results = dir_info["results"]
        dir_artifacts = dir_info["artifacts"]
        dir_logs = dir_info["logs"]
        if self.container_id:
            container.copy_file_from_container(
                self.container_id, self.dir_output, dir_results
            )
            container.copy_file_from_container(
                self.container_id, self.dir_logs, dir_results
            )
            container.copy_file_from_container(
                self.container_id, self.dir_output, dir_artifacts
            )
        else:
            save_command = "cp -rf {}/* {};".format(self.dir_output, dir_results)
            if self.dir_logs != "":
                save_command += "cp -rf {}/* {};".format(self.dir_logs, dir_results)
            if dir_artifacts != "":
                save_command += "cp -rf {}/* {};".format(self.dir_output, dir_artifacts)
            if dir_logs != "":
                save_command += "cp -rf {}/* {}".format(self.dir_logs, dir_logs)

            execute_command(save_command)

    def read_file(self, file_path, encoding="utf-8"):
        return abstractions.read_file(self.container_id, file_path, encoding)

    def read_json(self, file_path, encoding="utf-8"):
        return abstractions.read_json(self.container_id, file_path, encoding)

    def append_file(self, content, file_path):
        return abstractions.append_file(self.container_id, content, file_path)

    def write_file(self, content, file_path):
        return abstractions.write_file(self.container_id, content, file_path)

    def write_json(self, data, file_path):
        return abstractions.write_json(self.container_id, data, file_path)

    def list_dir(self, dir_path, regex=None):
        return abstractions.list_dir(self.container_id, dir_path, regex)

    def is_dir(self, dir_path):
        return abstractions.is_dir(self.container_id, dir_path)

    def is_file(self, file_path):
        return abstractions.is_file(self.container_id, file_path)

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

    def emit_normal(self, abstraction, concrete, message):
        super().emit_normal(abstraction, concrete, message)

    def emit_warning(self, abstraction, concrete, message):
        super().emit_warning(abstraction, concrete, message)

    def emit_error(self, abstraction, concrete, message):
        super().emit_error(abstraction, concrete, message)

    def emit_highlight(self, abstraction, concrete, message):
        super().emit_highlight(abstraction, concrete, message)

    def emit_success(self, abstraction, concrete, message):
        super().emit_success(abstraction, concrete, message)

    def emit_debug(self, abstraction, concrete, message):
        super().emit_debug(abstraction, concrete, message)
