import abc
import json
import os
import shutil
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional

from app.core import abstractions
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.metadata.MetadataLoader import MetadataLoader
from app.core.metadata.MetadataValidationSchemas import general_section_schema
from app.core.task.stats.BenchmarkStats import BenchmarkStats
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.AbstractDriver import AbstractDriver


class AbstractBenchmark(AbstractDriver):
    rebuilt_benchmarks: Dict[str, bool] = {}
    experiment_subjects: List[Any] = []
    meta_file: Optional[str] = None
    bench_dir_path = None

    name: str = ""
    image_name: str = ""

    __dir_info: DirectoryInfo = dict()

    dir_logs = ""
    dir_expr = ""
    dir_base_expr = ""
    dir_inst = ""
    dir_setup = ""

    log_dir_path = "None"
    log_deps_path = "None"
    log_deploy_path = "None"
    log_config_path = "None"
    log_build_path = "None"
    log_test_path = "None"

    size = 0
    list_artifact_dirs: List[str] = []
    list_artifact_files: List[str] = []
    base_dir_experiment = values.container_base_experiment

    key_bug_id = definitions.KEY_BUG_ID
    key_fix_file = definitions.KEY_FIX_FILE
    key_localization = definitions.KEY_LOCALIZATION
    key_failing_test_identifiers = definitions.KEY_FAILING_TEST
    key_passing_test_identifiers = definitions.KEY_PASSING_TEST
    key_java_version = definitions.KEY_JAVA_VERSION
    key_compile_cmd = definitions.KEY_COMPILE_CMD
    key_build_system = definitions.KEY_BUILD_SYSTEM
    key_fail_mod_dir = definitions.KEY_FAILING_MODULE_DIRECTORY
    key_test_all_cmd = definitions.KEY_TEST_ALL_CMD
    key_test_script = definitions.KEY_TEST_SCRIPT
    key_dir_class = definitions.KEY_CLASS_DIRECTORY
    key_dir_source = definitions.KEY_SOURCE_DIRECTORY
    key_dir_tests = definitions.KEY_TEST_DIRECTORY
    key_dir_test_class = definitions.KEY_TEST_CLASS_DIRECTORY
    key_commit_buggy = definitions.KEY_COMMIT_BUGGY
    key_commit_fix = definitions.KEY_COMMIT_FIX
    key_commit_checkout = definitions.KEY_COMMIT_CHECKOUT
    key_test_timeout = definitions.KEY_TEST_TIMEOUT
    key_subject = definitions.KEY_SUBJECT
    key_language = definitions.KEY_LANGUAGE
    has_standard_name: bool = False

    def __init__(self) -> None:
        self.dir_benchmark: str = values.dir_benchmark
        self.bench_dir_path = os.path.abspath(values.dir_benchmark)
        self.stats = BenchmarkStats()
        self.pre_built = False

        if not self.name:
            utilities.error_exit(
                "Concrete benchmark has not instantiated the name field. Aborting..."
            )
        AbstractBenchmark.check_benchmark_folder(self.name)
        self.meta_file = join(self.bench_dir_path, self.name, "meta-data.json")
        if self.image_name == "":
            self.has_standard_name = True
            self.image_name = "{}-benchmark".format(self.name)
        if values.use_container:
            self.build_benchmark_image()
        self.load_meta_file()
        self.use_valkyrie = values.use_valkyrie

    def read_file(
        self, container_id: Optional[str], file_path: str, encoding: str = "utf-8"
    ) -> List[str]:
        return abstractions.read_file(container_id, file_path, encoding)

    def append_file(
        self, container_id: Optional[str], content: List[str], file_path: str
    ) -> None:
        return abstractions.append_file(container_id, content, file_path)

    def _update_container_stats(self, container_id: str) -> None:
        container_stats = container.get_container_stats(container_id)
        if container_stats:
            self.stats.container_stats.load_container_stats(container_stats)

    def print_stats(self) -> None:
        emitter.highlight("\t\t\t deployed: {0}\n".format(self.stats.deployed))
        emitter.highlight("\t\t\t configured: {0}\n".format(self.stats.configured))
        emitter.highlight("\t\t\t built: {0}\n".format(self.stats.built))
        emitter.highlight("\t\t\t tested: {0}\n".format(self.stats.tested))

    def update_dir_info(self, dir_info: DirectoryInfo, locally_running: bool) -> None:
        self.__dir_info = dir_info
        if values.use_container and not locally_running:
            self.dir_expr = dir_info["container"]["experiment"]
            self.dir_logs = dir_info["container"]["logs"]
            self.dir_setup = dir_info["container"]["setup"]
            self.dir_base_expr = values.container_base_experiment
        else:
            self.dir_expr = dir_info["local"]["experiment"]
            self.dir_logs = dir_info["local"]["logs"]
            self.dir_setup = dir_info["local"]["setup"]
            self.dir_base_expr = values.dir_experiments

    def get_list(self) -> List[Any]:
        return self.experiment_subjects

    @staticmethod
    def load_meta_file_static(path: str, name: str) -> List[Any]:
        meta_file_path = join(path, name, "meta-data.json")
        AbstractBenchmark.check_benchmark_folder(name)
        try:
            loader = MetadataLoader(meta_file_path, general_section_schema)
            loader.load()
            loader.validate()
            return AbstractBenchmark.process_metadata(loader.get_meta_data())
        except Exception as e:
            values.experiment_status.set(TaskStatus.FAIL_IN_SETUP)
            utilities.error_exit(
                "Could not load meta-data from {}. Reason is {}".format(
                    meta_file_path, e
                )
            )

    @staticmethod
    def process_metadata(data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        for experiment_item in data:
            passing_list = experiment_item.get(
                AbstractBenchmark.key_passing_test_identifiers, []
            )
            failing_list = experiment_item.get(
                AbstractBenchmark.key_failing_test_identifiers, []
            )
            passing_list_str = [f"{x}" for x in passing_list]
            failing_list_str = [f"{x}" for x in failing_list]
            experiment_item[AbstractBenchmark.key_passing_test_identifiers] = (
                passing_list_str
            )
            experiment_item[AbstractBenchmark.key_failing_test_identifiers] = (
                failing_list_str
            )
        return data

    @staticmethod
    def check_benchmark_folder(name: str) -> None:
        if len(os.listdir(join(values.dir_benchmark, name))) == 0:
            emitter.information(
                "(information) Benchmark folder is empty. Probably submodule was not pulled. Pulling now.."
            )
            if (
                utilities.execute_command(
                    f"timeout -k 5s 10s 'git submodule update --init benchmark/{name}'",
                    directory=values.dir_main,
                )
                != 0
            ):
                utilities.error_exit(
                    "Could not get the submodule. Maybe the system asked for an SSH key and it could not be provided."
                )

    def load_meta_file(self) -> None:
        emitter.normal("\t[framework] loading experiment meta-data")
        if not self.meta_file:
            utilities.error_exit("Meta file path not set")
        if not os.path.isfile(self.meta_file):
            utilities.error_exit("Meta file does not exist")

        meta_file_loc = self.meta_file

        if values.special_meta:
            meta_file_loc = values.special_meta
            if not os.path.exists(meta_file_loc):
                utilities.error_exit("Special meta file path is incorrect")

        try:
            loader = MetadataLoader(meta_file_loc, general_section_schema)
            loader.load()
            loader.validate()
            self.experiment_subjects = AbstractBenchmark.process_metadata(
                loader.get_meta_data()
            )
            self.size = len(self.experiment_subjects)
        except Exception as e:
            values.experiment_status.set(TaskStatus.FAIL_IN_SETUP)
            utilities.error_exit(
                "Could not load meta-data from {}. Reason is {}".format(
                    meta_file_loc, e
                )
            )

    def run_command(
        self,
        container_id: Optional[str],
        command_str: str,
        log_file_path: str = "/dev/null",
        dir_path: str = values.container_base_experiment,
        env: Dict[str, str] = dict(),
    ) -> int:
        if container_id:
            exit_code, output = container.exec_command(
                container_id, command_str, dir_path, env
            )
            if output:
                stdout, stderr = output
                if "/dev/null" not in log_file_path:
                    self.append_file(container_id, [command_str, "\n"], log_file_path)

                    if stdout:
                        self.append_file(
                            container_id, [stdout.decode("iso-8859-1")], log_file_path
                        )
                    if stderr:
                        self.append_file(
                            container_id, [stderr.decode("iso-8859-1")], log_file_path
                        )
        else:
            command_str += " | tee -a {0} 2>&1".format(log_file_path)
            exit_code = utilities.execute_command(command_str, directory=dir_path)
        return exit_code

    def build_benchmark_image(self) -> None:
        if not container.image_exists(self.image_name) or (
            values.rebuild_all and self.name not in AbstractBenchmark.rebuilt_benchmarks
        ):
            if not container.image_exists(self.image_name):
                emitter.warning(
                    f"\t[framework] benchmark environment not found for {self.image_name}"
                )
            if values.rebuild_all:
                emitter.warning(
                    f"\t[framework] rebuilding benchmark environment for {self.image_name}"
                )
                AbstractBenchmark.rebuilt_benchmarks[self.name] = True
            if self.has_standard_name or not container.pull_image(
                self.image_name, "latest"
            ):
                emitter.normal("\t[framework] building benchmark environment")
                container.build_benchmark_image(self.image_name)
        else:
            emitter.success("\t\t[framework] pre-built benchmark environment found")

    def build_experiment_image(
        self,
        bug_index: int,
        test_all: bool,
        exp_image_name: str,
        cpu: List[str],
        gpu: List[str],
    ) -> None:
        """
        Builds an image for an experiment
        """
        container_id = self.setup_container(bug_index, self.image_name, cpu, gpu)
        is_error = self.setup_experiment(bug_index, container_id, test_all)
        if is_error:
            self.emit_error("setting up experiment failed")
        if not container_id:
            self.error_exit("could not setup container correctly")
        else:
            container_obj: Any = container.get_container(container_id)
            container_obj.commit(exp_image_name)
            container.stop_container(container_id, 5)
            if not values.debug:
                container.remove_container(container_id)

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = None
        emitter.normal("\t\t[framework] preparing experiment environment")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        dir_exp_local = join(values.dir_experiments, self.name, subject_name, bug_id)

        if os.path.isdir(dir_exp_local):
            shutil.rmtree(dir_exp_local)

        volume_list = {
            self.__dir_info["local"]["setup"]: {"bind": "/scripts", "mode": "rw"},
            os.path.join(self.__dir_info["local"]["setup"], "../..", "base"): {
                "bind": join(self.dir_expr, "base"),
                "mode": "rw",
            },
            os.path.join(self.__dir_info["local"]["setup"], "../..", ".aux"): {
                "bind": join(self.dir_expr, ".aux"),
                "mode": "rw",
            },
        }

        container_name = "-".join([self.name, subject_name, bug_id]).lower()
        container_id = container.get_container_id(container_name, ignore_not_found=True)
        if container_id:
            container.kill_container(container_id, ignore_errors=True)
            container.remove_container(container_id)
        container_id = container.build_container(
            container_name, volume_list, image_name, cpu, gpu
        )
        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        copy_local_cmd = "cp -rf {} {}".format("/scripts", self.dir_setup)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        self.run_command(container_id, copy_local_cmd, "/dev/null", "/")
        return container_id

    def _handle_setup_exp_error(
        self, task_status: TaskStatus, error_msg: str, container_id: Optional[str]
    ) -> bool:
        values.experiment_status.set(task_status)
        self.emit_error(error_msg)
        if container_id:
            self._update_container_stats(container_id)

        return True

    def setup_experiment(
        self, bug_index: int, container_id: Optional[str], test_all: bool
    ) -> bool:
        self.emit_normal("preparing experiment subject")
        if not container_id:
            self.base_dir_experiment = os.path.abspath(values.dir_experiments)
            if os.path.isdir(self.dir_expr):
                utilities.execute_command("rm -rf {}".format(self.dir_expr))
            if not os.path.isdir(self.dir_logs):
                utilities.execute_command("mkdir -p {}".format(self.dir_logs))
        else:
            if not container.is_dir(container_id, self.dir_logs):
                self.run_command(
                    container_id, "mkdir -p {}".format(self.dir_logs), dir_path="/"
                )

        # init log paths
        self.log_deps_path = join(
            self.dir_logs, f"{self.name}-{str(bug_index)}-deps.log"
        )
        self.log_deploy_path = join(
            self.dir_logs, f"{self.name}-{str(bug_index)}-deploy.log"
        )
        self.log_config_path = join(
            self.dir_logs, f"{self.name}-{str(bug_index)}-config.log"
        )
        self.log_build_path = join(
            self.dir_logs, f"{self.name}-{str(bug_index)}-build.log"
        )
        self.log_test_path = join(
            self.dir_logs, f"{self.name}-{str(bug_index)}-test.log"
        )

        self.stats.deployed = self.deploy(bug_index, container_id)
        if not self.stats.deployed:
            return self._handle_setup_exp_error(
                TaskStatus.FAIL_IN_DEPLOY, "deploy failed", container_id
            )
        self.stats.configured = self.config(bug_index, container_id)
        if not self.stats.configured:
            return self._handle_setup_exp_error(
                TaskStatus.FAIL_IN_CONFIG, "config failed", container_id
            )
        self.stats.built = self.build(bug_index, container_id)
        if not self.stats.built:
            return self._handle_setup_exp_error(
                TaskStatus.FAIL_IN_BUILD, "build failed", container_id
            )

        test_choice = self.test_all if test_all else self.test

        self.stats.tested = test_choice(bug_index, container_id)
        if not self.stats.tested:
            return self._handle_setup_exp_error(
                TaskStatus.FAIL_IN_TEST, "testing failed", container_id
            )

        self.emit_success("setting up completed successfully")
        return False

    def get_exp_image(
        self,
        bug_index: int,
        test_all: bool,
        cpu: List[str],
        gpu: List[str],
        ignore_rebuild: bool = False,
    ) -> str:
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        exp_image_name = "{}-{}-{}".format(self.name, subject_name, bug_id).lower()
        if not container.image_exists(exp_image_name) or (
            not ignore_rebuild and values.rebuild_all
        ):
            emitter.warning(
                "\t\t[framework][WARNING] experiment subject {} with bug name {} is not built or is needed to be rebuilt".format(
                    subject_name, bug_id
                )
            )
            emitter.normal("\t\t\t[framework] preparing/building said experiment")
            self.build_experiment_image(bug_index, test_all, exp_image_name, cpu, gpu)
        else:
            emitter.success(
                "\t\t[framework] pre-built experiment image found: {}".format(
                    exp_image_name
                )
            )
            self.pre_built = True
        return exp_image_name

    @abc.abstractmethod
    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        """Prepares the experiment, e.g. download or copy and synthesize an image for the bug from the benchmark"""
        return False

    # @abc.abstractmethod
    # def deps(self, bug_index, container_id: Optional[str]):
    #     """Prepares the environment with dependencies, e.g. install using apt-get"""
    #     return

    @abc.abstractmethod
    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        """Configure the bug from the benchmark, e.g. running the ./configure script for a C/C++ project"""
        return False

    @abc.abstractmethod
    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        """Builds the bug from the benchmark, e.g. invoking the make command for a C/C++ project or ant/mvn package/gradle build for a Java project"""
        return False

    @abc.abstractmethod
    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        """Runs a single test for a bug from the benchmark"""
        return False

    @abc.abstractmethod
    def test_all(self, bug_index: int, container_id: Optional[str]) -> bool:
        """Runs all tests for a bug in the benchmark"""
        return False

    @abc.abstractmethod
    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        """Save all artifacts produced by the tool"""
        self.emit_normal("saving experiment artifacts")
        if container_id:
            dir_exp = dir_info["container"]["experiment"]
            dir_artifact = dir_info["container"]["artifacts"]
        else:
            dir_exp = dir_info["local"]["experiment"]
            dir_artifact = dir_info["local"]["artifacts"]

        if self.list_artifact_dirs:
            for art_dir in self.list_artifact_dirs:
                art_dir_path = join(dir_exp, art_dir)
                copy_command = "cp -rf {} {}".format(art_dir_path, dir_artifact)
                self.run_command(container_id, copy_command, "/dev/null", "/")

        if self.list_artifact_files:
            for art_file in self.list_artifact_files:
                art_file_path = join(dir_exp, art_file)
                copy_command = "cp -f {} {}".format(art_file_path, dir_artifact)
                self.run_command(container_id, copy_command, "/dev/null", "/")
        return

    @abc.abstractmethod
    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        """Clean up any residual files. This method is used for the case where Cerberus has been ran locally."""
        return

    def emit_normal(self, message: Any) -> None:
        self._emit_normal_raw("benchmark", self.name, message)

    def emit_warning(self, message: Any) -> None:
        self._emit_warning_raw("benchmark", self.name, message)

    def emit_error(self, message: Any) -> None:
        self._emit_error_raw("benchmark", self.name, message)

    def emit_highlight(self, message: Any) -> None:
        self._emit_highlight_raw("benchmark", self.name, message)

    def emit_success(self, message: Any) -> None:
        self._emit_success_raw("benchmark", self.name, message)

    def emit_debug(self, message: Any) -> None:
        self._emit_debug_raw("benchmark", self.name, message)

    def is_dir(self, dir_path: str, container_id: Optional[str]) -> bool:
        return abstractions.is_dir(container_id, dir_path)

    def is_file(self, file_path: str, container_id: Optional[str]) -> bool:
        return abstractions.is_file(container_id, file_path)
