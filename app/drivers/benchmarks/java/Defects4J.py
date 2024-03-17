import os
from os.path import join
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Defects4J(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Defects4J, self).__init__()

    def setup_container(
        self, bug_index: int, image_name: str, cpu: List[str], gpu: List[str]
    ) -> Optional[str]:
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """
        container_id = super(Defects4J, self).setup_container(
            bug_index, image_name, cpu, gpu
        )
        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        return container_id

    def deploy(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("downloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[self.key_bug_id]).split("-")[-1]
        custom_env = {"JAVA_TOOL_OPTIONS": "-Dfile.encoding=UTF8"}
        command_str = "defects4j checkout -p {} -v {}b -w {}".format(
            experiment_item[self.key_subject],
            bug_id,
            join(self.dir_expr, "src"),
        )
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, env=custom_env
        )
        self.run_command(
            container_id,
            "defects4j export -p cp.test -o classpath_data",
            self.log_deploy_path,
            join(self.dir_expr, "src"),
            custom_env,
        )
        for dependency in self.read_file(
            container_id, join(self.dir_expr, "src", "classpath_data")
        )[0].split(":"):
            if dependency.startswith("/defects4j"):
                source = dependency
                destination = "{}/deps/{}".format(
                    self.dir_expr, dependency.split("/defects4j/framework/projects/")[1]
                )
                self.run_command(
                    container_id,
                    "mkdir -p {}".format(os.path.dirname(destination)),
                    log_file_path=self.log_deploy_path,
                )
                self.run_command(
                    container_id,
                    "cp {} {}".format(source, destination),
                    log_file_path=self.log_deploy_path,
                )

        return status == 0

    def config(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("configuring experiment subject")
        return True

    def build(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("building experiment subject")
        custom_env = {"JAVA_TOOL_OPTIONS": "-Dfile.encoding=UTF8"}
        command_str = "defects4j compile"
        status = self.run_command(
            container_id,
            command_str,
            self.log_build_path,
            join(self.dir_expr, "src"),
            custom_env,
        )
        return status == 0

    def test(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("testing experiment subject")
        command_str = "defects4j test"
        status = self.run_command(
            container_id, command_str, self.log_deploy_path, join(self.dir_expr, "src")
        )
        return status == 0

    def clean(self, exp_dir_path: str, container_id: Optional[str]) -> None:
        self.emit_normal("removing experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(
        self, dir_info: DirectoryInfo, container_id: Optional[str]
    ) -> None:
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Defects4J, self).save_artifacts(dir_info, container_id)
