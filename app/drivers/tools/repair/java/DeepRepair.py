import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class DeepRepair(AbstractRepairTool):

    astor_home = "/opt/astor"
    astor_version = "2.0.0"

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/astor"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(task_config_info[self.key_timeout])

        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = bug_info["class_directory"]
        dir_test_bin = bug_info["test_class_directory"]
        list_deps = bug_info["dependencies"]
        list_deps.append(f"{self.astor_home}/external/lib/hamcrest-core-1.3.jar")
        list_deps.append(f"{self.astor_home}/external/lib/junit-4.11.jar")
        list_deps_str = ":".join(list_deps)

        # generate patches
        self.timestamp_log_start()
        repair_command = (
            f"timeout -k 5m {timeout_h}h "
            f"java -cp target/astor-{self.astor_version}-jar-with-dependencies.jar "
            f"fr.inria.main.evolution.AstorMain "
            f"-mode deeprepair "
            f"-srcjavafolder {dir_java_src} "
            f"-srctestfolder {dir_test_src}  "
            f"-binjavafolder {dir_java_bin} "
            f"-bintestfolder  {dir_test_bin} "
            f"-location {self.dir_expr}/src "
            f"-dependencies {list_deps_str}"
        )

        status = self.run_command(repair_command, self.log_output_path, self.astor_home)

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        list_artifact_dirs = [
            self.astor_home + "/" + x for x in ["diffSolutions", "output_astor"]
        ]
        for d in list_artifact_dirs:
            copy_command = f"cp -rf {d} {self.dir_output}"
            self.run_command(copy_command)
        super(DeepRepair, self).save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        self.emit_normal("reading output")

        count_plausible = 0
        count_enumerations = 0
        count_compilable = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "child compiles" in line.lower():
                    count_compilable += 1
                    identifier = re.search(r"id (.*)", line)
                    if not identifier:
                        self.emit_warning("Could not find id")
                        continue
                    child_id = int(str(identifier.group(1)).strip())
                    if child_id > count_enumerations:
                        count_enumerations = child_id
                elif "found solution," in line.lower():
                    count_plausible += 1

        self.stats.patch_stats.generated = len(
            [
                x
                for x in self.list_dir(join(self.astor_home, "diffSolutions"))
                if ".diff" in x
            ]
        )
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.non_compilable = count_enumerations - count_compilable

        return self.stats
