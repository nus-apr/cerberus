import abc
import os
import re
import shutil
import time
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional
from typing import Sequence
from typing import Tuple

from app.core import abstractions
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.core.utilities import execute_command
from app.drivers.AbstractDriver import AbstractDriver
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.ui import ui


class AbstractTool(AbstractDriver):
    log_instrument_path = ""
    log_output_path = ""

    image_name = ""
    name = ""
    tool_tag = ""

    dir_logs = ""
    dir_output = ""
    dir_expr = ""
    dir_base_expr = ""
    dir_inst = ""
    dir_setup = ""

    cpu_usage = 1
    gpu_usage = 0
    hash_digest = ""
    container_id: Optional[str] = None
    is_instrument_only = False
    timestamp_fmt = "%a %d %b %Y %H:%M:%S %p"
    current_task_profile_id = values.current_task_profile_id

    # region Keys
    key_benchmark = definitions.KEY_BENCHMARK
    key_subject = definitions.KEY_SUBJECT
    key_language = definitions.KEY_LANGUAGE
    key_id = definitions.KEY_ID
    key_bug_id = definitions.KEY_BUG_ID
    key_bug_type = definitions.KEY_BUG_TYPE
    key_tool_params = definitions.KEY_TOOL_PARAMS
    key_tool_name = definitions.KEY_TOOL_NAME
    key_timeout = definitions.KEY_CONFIG_TIMEOUT
    key_source = definitions.KEY_SOURCE
    key_fix_file = definitions.KEY_FIX_FILE
    key_fix_lines = definitions.KEY_FIX_LINES
    key_fix_loc = definitions.KEY_FIX_LOC
    key_localization = definitions.KEY_LOCALIZATION
    key_sink = definitions.KEY_SINK
    key_compile_programs = definitions.KEY_COMPILE_PROGRAMS
    key_build_command_project = definitions.KEY_BUILD_COMMAND_PROJECT
    key_build_command_repair = definitions.KEY_BUILD_COMMAND_REPAIR
    key_build_command = definitions.KEY_BUILD_COMMAND
    key_clean_command = definitions.KEY_CLEAN_COMMAND
    key_config_command = definitions.KEY_CONFIG_COMMAND
    key_build_script = definitions.KEY_BUILD_SCRIPT
    key_config_script = definitions.KEY_CONFIG_SCRIPT
    key_test_script = definitions.KEY_TEST_SCRIPT
    key_clean_script = definitions.KEY_CLEAN_SCRIPT
    key_failing_test_identifiers = definitions.KEY_FAILING_TEST
    key_passing_test_identifiers = definitions.KEY_PASSING_TEST
    key_exploit_inputs = definitions.KEY_EXPLOIT_INPUTS
    key_benign_inputs = definitions.KEY_BENIGN_INPUTS
    key_pub_test_script = definitions.KEY_PUB_TEST_SCRIPT
    key_pvt_test_script = definitions.KEY_PVT_TEST_SCRIPT
    key_adv_test_script = definitions.KEY_ADV_TEST_SCRIPT
    key_dir_class = definitions.KEY_CLASS_DIRECTORY
    key_dir_source = definitions.KEY_SOURCE_DIRECTORY
    key_dir_tests = definitions.KEY_TEST_DIRECTORY
    key_dir_test_class = definitions.KEY_TEST_CLASS_DIRECTORY
    key_gpus = definitions.KEY_GPUS
    key_cpus = definitions.KEY_CPUS
    key_analysis_output = definitions.KEY_ANALYSIS_OUTPUT
    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES
    key_java_version = definitions.KEY_JAVA_VERSION
    key_generator = definitions.KEY_GENERATOR
    key_stack_trace = definitions.KEY_STACK_TRACE
    key_build_system = definitions.KEY_BUILD_SYSTEM
    # endregion

    stats: ToolStats
    tool_type: str

    locally_running: bool = False

    bindings: Optional[Dict[str, Any]] = None
    runs_as_root: bool = True
    sudo_password: str = ""
    image_user: str = "root"
    command_history: List[Tuple[str, str, Dict[str, str]]]

    required_fields = ["stats", "tool_type"]

    def __init__(self, tool_name: str) -> None:
        """add initialization commands to all tools here"""
        super().__init__()
        self.name = tool_name
        for required_field in AbstractTool.required_fields:
            if not hasattr(self, required_field):
                self.error_exit(
                    "{} should be set in the subtype tool constructor!".format(
                        required_field
                    )
                )
        self.command_history = []
        self.portable_dirs: List[str] = []
        self.path_to_binaries: List[str] = []
        self.is_ui_active = values.ui_active
        self.is_only_instrument = values.only_instrument
        self.is_debug = values.debug
        self.is_dump_patches = values.dump_patches
        self.use_container = values.use_container
        self.use_valkyrie = values.use_valkyrie
        self.use_gpu = values.use_gpu

    @abc.abstractmethod
    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        The following method should be implemented by the tool driver.
        It is the main entrypoint for the tool.
        """
        pass

    def invoke_advanced(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info: Dict[str, Any],
        task_config_info: Dict[str, Any],
        container_config_info: Dict[str, Any],
        run_index: str,
        hash: str,
    ) -> None:
        """
        The following method is invoked by Cerberus internally to run the tool.
        Only modify it if you need the arguments.
        The default implementation (currently only changed by composite tool) just calls invoke.
        """
        self.emit_normal(
            "Invoking tool {} on experiment subject {} with bug id {}".format(
                self.name, bug_info[self.key_subject], bug_info[self.key_bug_id]
            )
        )
        utilities.check_space()
        self.emit_normal("Preprocessing")
        self.pre_process(bug_info)

        self.instrument(bug_info)
        self.emit_normal("Executing invoke command")

        bug_id = str(bug_info[definitions.KEY_BUG_ID])

        log_file_name = "{}-{}-{}-output.log".format(
            task_config_info[definitions.KEY_ID], self.name.lower(), bug_id
        )
        self.extract_fields_to_stats(bug_info, task_config_info)
        bug_info["tool-name"] = self.name
        task_config_info["container-id"] = self.container_id

        self.log_output_path = os.path.join(self.dir_logs, log_file_name)

        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")

        self.invoke(bug_info, task_config_info)

    def extract_fields_to_stats(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        filtered_bug_info = dict()
        interested_keys = [
            self.key_id,
            self.key_bug_id,
            self.key_subject,
            self.key_benchmark,
            definitions.KEY_COUNT_NEG,
            definitions.KEY_COUNT_POS,
        ]
        for k in interested_keys:
            filtered_bug_info[k] = bug_info.get(k, None)
        self.stats.bug_info = filtered_bug_info
        self.stats.config_info = task_config_info

    def instrument(self, bug_info: Dict[str, Any]) -> None:
        """instrumentation for the experiment as needed by the tool"""
        if not self.is_file(join(self.dir_inst, "instrument.sh")):
            return
        self.emit_normal("Running instrumentation script")
        bug_id = bug_info[definitions.KEY_BUG_ID]
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        buggy_file = bug_info.get(self.key_localization, [{}])[0].get(
            definitions.KEY_FIX_FILE, ""
        )
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(task_conf_id, self.name, bug_id),
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        self.emit_debug(
            "\t\t\t instrumentation took {} second(s)".format(
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

    @abc.abstractmethod
    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> ToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are dependent on the fields of the subtype of ToolStats
        """
        return self.stats

    def clean_up(self) -> None:
        if self.container_id:
            container.remove_container(self.container_id)
        else:
            if os.path.isdir(self.dir_expr):
                rm_command = "rm -rf {}".format(self.dir_expr)
                execute_command(rm_command)

    def process_tests(
        self,
        dir_info: DirectoryInfo,
        config_info: Dict[str, Any],
        bug_info: Dict[str, Any],
    ) -> None:
        for test_group, identifier_key, len_key, config_count in [
            (
                self.key_benign_inputs,
                self.key_passing_test_identifiers,
                definitions.KEY_COUNT_POS,
                definitions.KEY_CONFIG_PASSING_TEST_COUNT,
            ),
            (
                self.key_exploit_inputs,
                self.key_failing_test_identifiers,
                definitions.KEY_COUNT_NEG,
                definitions.KEY_CONFIG_FAILING_TEST_COUNT,
            ),
        ]:
            patched_jazzer = False
            for analysis_result in bug_info.get(self.key_analysis_output, []):
                for tests in analysis_result.get(test_group, []):
                    """
                    Documents how to process tests to ensure their usability
                    """
                    if tests["format"] == "junit":
                        if not patched_jazzer:
                            patched_jazzer = True
                            jazzer_dep = """<dependency><groupId>com.code-intelligence</groupId><artifactId>jazzer</artifactId><version>0.22.1</version></dependency>"""

                            self.run_command(
                                "find {} -name pom.xml -exec sed -i 's|</dependencies>|{}</dependencies>|g' {{}} ;".format(
                                    join(self.dir_expr, "src"), jazzer_dep
                                )
                            )

                        test_limit = config_info.get(config_count, -1)
                        if test_limit != -1:
                            self.run_command(
                                "bash -c \"find ./ -type f | head -n {0} | xargs -I[] bash -c 'mkdir -p {1}/$(dirname []); cp [] {1}/[]' \"".format(
                                    test_limit,
                                    join(
                                        self.dir_expr,
                                        "src",
                                        bug_info[self.key_dir_tests],
                                    ),
                                ),
                                dir_path=join(self.dir_setup, tests["dir"]),
                            )
                        else:
                            self.run_command(
                                "bash -c 'cp -r {}/. {}'".format(
                                    join(self.dir_setup, tests["dir"]),
                                    join(
                                        self.dir_expr,
                                        "src",
                                        bug_info[self.key_dir_tests],
                                    ),
                                )
                            )
                    if tests["format"] == "raw":
                        # TODO make recursive
                        # Remove the .state file just in case
                        test_dir_path = join(dir_info["local"]["setup"], tests["dir"])
                        test_identifiers = []
                        if os.path.exists(test_dir_path):
                            test_identifiers = list(
                                filter(
                                    lambda x: not x.startswith("."),
                                    os.listdir(test_dir_path),
                                )
                            )
                        bug_info[identifier_key] = list(
                            set(bug_info.get(identifier_key, []) + test_identifiers)
                        )
                        bug_info[len_key] = len(bug_info[identifier_key])
                        self.run_command(
                            "bash -c 'cp -r {}/. {}'".format(
                                join(self.dir_setup, tests["dir"]),
                                join(self.dir_setup, "tests"),
                            )
                        )
                        self.run_command(
                            "bash -c 'rm .??*'", dir_path=join(self.dir_setup, "tests")
                        )
                        pass
                    if tests["format"] == "ktest":
                        self.emit_warning("Not supporting ktest files yet!")
                        pass
        self.write_json([bug_info], join(self.dir_base_expr, "meta-data.json"))
        pass

    def update_info(
        self,
        container_id: Optional[str],
        instrument_only: bool,
        dir_info: DirectoryInfo,
        experiment_info: Dict[str, Any],
    ) -> None:
        self.container_id = container_id
        self.is_instrument_only = instrument_only
        self.update_dir_info(dir_info)
        self.update_experiment_info(experiment_info)

        experiment_info[definitions.KEY_OUTPUT_DIR_ABSPATH] = self.dir_output

    def update_experiment_info(self, experiment_info: Dict[str, Any]) -> None:
        self.write_json([experiment_info], join(self.dir_base_expr, "meta-data.json"))

    def update_container_stats(self, container_id: str) -> None:
        container_stats = container.get_container_stats(container_id)
        if container_stats:
            self.stats.container_stats.load_container_stats(container_stats)

    def update_dir_info(self, dir_info: DirectoryInfo) -> None:
        if self.container_id:
            self.dir_expr = dir_info["container"]["experiment"]
            self.dir_logs = dir_info["container"]["logs"]
            self.dir_inst = dir_info["container"]["instrumentation"]
            self.dir_setup = dir_info["container"]["setup"]
            self.dir_output = dir_info["container"]["artifacts"]
            self.dir_base_expr = values.container_base_experiment
        else:
            self.dir_expr = dir_info["local"]["experiment"]
            self.dir_logs = dir_info["local"]["logs"]
            self.dir_inst = dir_info["local"]["instrumentation"]
            self.dir_setup = dir_info["local"]["setup"]
            self.dir_output = dir_info["local"]["artifacts"]
            self.dir_base_expr = values.dir_experiments

        self.dir_patch = join(
            self.dir_output,
            "patch-valid" if self.use_valkyrie else "patches",
        )
        self.dir_selection = join(self.dir_output, "selection")
        self.dir_localization = join(self.dir_output, "localization")

    def timestamp_log(self) -> None:
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"{time_now}"
        self.append_file([timestamp_txt], self.log_output_path)

    def timestamp_log_start(self) -> None:
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"{time_now}\n"
        self.append_file([timestamp_txt], self.log_output_path)
        self.stats.time_stats.timestamp_start = timestamp_txt

    def timestamp_log_end(self) -> None:
        time_now = time.strftime("%a %d %b %Y %H:%M:%S %p")
        timestamp_txt = f"\n{time_now}"
        self.append_file([timestamp_txt], self.log_output_path)
        self.stats.time_stats.timestamp_end = timestamp_txt

    def run_command(
        self,
        command: str,
        log_file_path: str = "/dev/null",
        dir_path: Optional[str] = None,
        env: Dict[str, str] = dict(),
    ) -> int:
        """executes the specified command at the given dir_path and save the output to log_file without returning the result"""
        if self.container_id:
            if not dir_path:
                dir_path = values.container_base_experiment
            exit_code, output = container.exec_command(
                self.container_id, command, dir_path, env
            )
            if output:
                stdout, stderr = output
                if "/dev/null" not in log_file_path:
                    if stdout:
                        self.append_file([stdout.decode("iso-8859-1")], log_file_path)
                    if stderr:
                        self.append_file([stderr.decode("iso-8859-1")], log_file_path)
        else:
            if not dir_path:
                dir_path = self.dir_expr
            command += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command, env=env, directory=dir_path)

        self.command_history.append((dir_path, command, env))
        return exit_code

    def exec_command(
        self,
        command: str,
        log_file_path: str = "/dev/null",
        dir_path: Optional[str] = None,
        env: Dict[str, str] = dict(),
    ) -> Tuple[int, Optional[Tuple[Optional[bytes], Optional[bytes]]]]:
        """executes the specified command at the given dir_path and save the output to log_file"""
        if self.container_id:
            if not dir_path:
                dir_path = values.container_base_experiment
            exit_code, output = container.exec_command(
                self.container_id, command, dir_path, env
            )
            if output:
                stdout, stderr = output
                if "/dev/null" not in log_file_path:
                    if stdout:
                        self.append_file([stdout.decode("iso-8859-1")], log_file_path)
                    if stderr:
                        self.append_file([stderr.decode("iso-8859-1")], log_file_path)
            return exit_code, output
        else:
            if not dir_path:
                dir_path = self.dir_expr
            command += " >> {0} 2>&1".format(log_file_path)
            exit_code = execute_command(command, env=env, directory=dir_path)

        self.command_history.append((dir_path, command, env))
        return exit_code, None

    def process_status(self, status: int) -> None:
        """Process the status of running a command"""
        if status != 0:
            self.stats.error_stats.is_error = True
            values.experiment_status.set(
                TaskStatus.FAIL_IN_TOOL if status != 124 else TaskStatus.TIMEOUT
            )
            emitter.warning(
                "\t\t\t[framework] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
            if (status == 137 or status == 124) and self.container_id:
                # Due to the container being killed, we restart it to be able to pull out the analysis info
                container.stop_container(self.container_id, 5)
                container.start_container(self.container_id)

        else:
            values.experiment_status.set(TaskStatus.SUCCESS)
            emitter.success(
                "\t\t\t[framework] {0} ended successfully".format(self.name)
            )

    def pre_process(self, bug_info: Dict[str, Any]) -> None:
        """Any pre-processing required for the tool"""
        # self.check_tool_exists()
        return

    def ensure_tool_exists(self, tag_name_default: str = "latest") -> None:
        """Check that the tool is available either as an image or locally"""

        def get_digest(image: Any) -> str:
            return "".join(
                next(iter(image.attrs.get("RepoDigests", [])), "@").split("@")[1:]
            )

        if values.use_container and not self.locally_running:
            if values.secure_hash:
                emitter.debug(
                    "\t[framework] will check whether the final image that is locally available aligns has a hash digest,starting with {}".format(
                        self.hash_digest
                    )
                )
                if self.hash_digest == "":
                    emitter.warning(
                        "\t[framework] hash is not set. Will pass without checks"
                    )
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
                tag_name = tag_name_default
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

                image_hash_digest = get_digest(image)

                if values.secure_hash and not image_hash_digest.startswith(
                    self.hash_digest
                ):
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
                local_image_hash_digest = get_digest(local_image)

                # Then try pulling. If it is the same one we are quick
                # If not we have to wait but it is safer than getting stale results.
                # In theory this has a supply chain vulnerability but we can assume
                # That the storage is safe
                if values.use_latest_image:
                    remote_image = container.pull_image(repo_name, tag_name)
                    remote_image_hash_digest = get_digest(remote_image)

                    if (
                        remote_image
                        and remote_image_hash_digest != local_image_hash_digest
                    ):
                        emitter.information(
                            "\t[framework] docker image {}:{} is not the same as the one in the repository. Will have to rebuild".format(
                                repo_name, tag_name
                            )
                        )
                        values.rebuild_all = True
                        if (
                            values.secure_hash
                            and not remote_image_hash_digest.startswith(
                                self.hash_digest
                            )
                        ):
                            utilities.error_exit(
                                "\t[framework] secure mode is enabled. aborting"
                            )
                else:
                    emitter.debug(
                        "\t[framework] checking local image {}".format(
                            local_image_hash_digest
                        )
                    )
                    if values.secure_hash and not local_image_hash_digest.startswith(
                        self.hash_digest
                    ):
                        utilities.error_exit(
                            "\t[framework] local image for {} hash a which does not align with the one in the driver. aborting".format(
                                self.name
                            )
                        )

        else:
            self.locate()
        return

    def locate(self) -> None:
        local_path = shutil.which(self.name.lower())
        if not local_path:
            error_exit("{} not Found".format(self.name))

    def update_experiment_status(self, status: str) -> None:
        """Update the status of the experiment if any visualization is available"""
        ui.update_current_job(status)

    def post_process(self) -> None:
        """Any post-processing required for the tool"""
        if self.container_id:
            container.stop_container(self.container_id)
        if values.use_purge:
            self.clean_up()
        return

    def print_stats(self) -> None:
        """Print the statistics of the tool."""
        self.stats.write(self.emit_highlight, "\t")
        pass

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
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

    # region File Operations

    def read_file(self, file_path: str, encoding: str = "utf-8") -> List[str]:
        return abstractions.read_file(self.container_id, file_path, encoding)

    def read_json(self, file_path: str, encoding: str = "utf-8") -> Optional[Any]:
        return abstractions.read_json(self.container_id, file_path, encoding)

    def append_file(self, content: Sequence[str], file_path: str) -> None:
        return abstractions.append_file(self.container_id, content, file_path)

    def write_file(self, content: Sequence[str], file_path: str) -> None:
        return abstractions.write_file(self.container_id, content, file_path)

    def write_json(self, data: Any, file_path: str) -> None:
        return abstractions.write_json(self.container_id, data, file_path)

    def list_dir(self, dir_path: str, regex: Optional[str] = None) -> List[str]:
        return abstractions.list_dir(self.container_id, dir_path, regex)

    def is_dir(self, dir_path: str) -> bool:
        return abstractions.is_dir(self.container_id, dir_path)

    def is_file(self, file_path: str) -> bool:
        return abstractions.is_file(self.container_id, file_path)

    def load_ast(
        self, file_path: str, encoding: str = "utf-8", language: str = "java"
    ) -> Any:
        return abstractions.load_ast(self.container_id, file_path, encoding, language)

    # endregion

    def get_output_log_path(self) -> str:
        # parse this file for time info
        if not self.log_output_path:
            regex = re.compile("(.*-output.log$)")
            for _, _, files in os.walk(self.dir_logs):
                for file in files:
                    if regex.match(file) and self.name in file:
                        self.log_output_path = os.path.join(self.dir_logs, file)
                        break
        return self.log_output_path

    def save_trace(self) -> None:
        """
        Captures all the executed commands
        """
        script_contents = [
            "#!/bin/bash\n",
            "#This script is used to save the trace of the tool\n",
        ]
        last_dir = ""
        for dir, command, env in self.command_history:
            if last_dir != dir:
                script_contents.append("cd {}\n".format(dir))
                last_dir = dir
            if env:
                script_contents.append(
                    "export {}\n".format(" ".join(f"{k}={v}" for k, v in env.items()))
                )
            script_contents.append("{}\n".format(command))

        self.write_file(script_contents, join(self.dir_expr, "trace.sh"))
        self.write_file(script_contents, join(self.dir_output, "trace.sh"))

    # region Emitters

    def emit_normal(self, message: Any) -> None:
        self._emit_normal_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_warning(self, message: Any) -> None:
        self._emit_warning_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_error(self, message: Any) -> None:
        self._emit_error_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_highlight(self, message: Any) -> None:
        self._emit_highlight_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_success(self, message: Any) -> None:
        self._emit_success_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_debug(self, message: Any) -> None:
        self._emit_debug_raw(
            self.tool_type,
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    # endregion

    def clean_subject(self, bug_info: Dict[str, Any]) -> None:
        self.emit_normal(f"cleaning subject")
        if bug_info.get(self.key_clean_script, None):
            clean_script = f"{self.dir_setup}/{bug_info[self.key_clean_script]}"
            clean_command = "bash {}".format(clean_script)
            log_clean_path = join(self.dir_logs, f"{self.name}-clean.log")
            self.run_command(clean_command, log_file_path=log_clean_path)
