import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Nopol(AbstractRepairTool):
    nopol_home = "/opt/nopol"
    nopol_version = "0.0.3"
    dir_source = ""

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/nopol"

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
        failing_test_identifiers_list = bug_info[self.key_failing_test_identifiers]
        dir_java_src = self.dir_expr + "/src/" + bug_info["source_directory"]
        self.dir_source = dir_java_src

        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])

        list_deps = [join(self.dir_expr, dep) for dep in bug_info["dependencies"]]
        list_deps.append(join(self.nopol_home, "nopol/lib/hamcrest-core-1.3.jar"))
        list_deps.append(join(self.nopol_home, "nopol/lib/junit-4.11.jar"))
        list_deps.append(dir_java_bin)
        list_deps.append(dir_test_bin)

        list_deps_str = ":".join(list_deps)

        test_classes_str = " ".join(failing_test_identifiers_list)
        nopol_jar_path = (
            f"{self.nopol_home}/nopol/nopol-{self.nopol_version}"
            f"-SNAPSHOT-jar-with-dependencies.jar"
        )

        solver_name = "z3"  # z3 or cvc4
        solver_path = f"{self.nopol_home}/nopol/lib/z3/z3_for_linux"
        max_generations = 2000000
        test_timeout = 30000
        # generate patches
        self.timestamp_log_start()
        repair_command = (
            f"timeout -k 5m {timeout_h}h java -jar {nopol_jar_path} nopol "
            f"{dir_java_src} "
            f"{list_deps_str} "
            f"{solver_name} "
            f"{solver_path} "
            f"{test_classes_str} "
        )

        status = self.run_command(repair_command, self.log_output_path, self.dir_output)

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

        patch_dir = f"{self.dir_source}/spoon"
        copy_command = "cp -rf {} {}".format(patch_dir, self.dir_output)
        self.run_command(copy_command)
        super(Nopol, self).save_artifacts(dir_info)

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
                if "Applying patch" in line:
                    count_enumerations += 1
                elif "PATCH FOUND" in line:
                    count_plausible += 1

        self.stats.patch_stats.generated = len(
            [x for x in self.list_dir(join(self.dir_source, "spooned")) if ".java" in x]
        )
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible

        return self.stats
