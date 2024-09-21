import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class APRER(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(APRER, self).__init__(self.name)
        self.image_name = "yeyehe/aprerupdate:latest"
        self.hash_digest = (
            "sha256:3d6436ea60fd29c28c65fb57479b94c666128a9d4f1c559f8cbfe01905669891"
        )

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        project_dir = self.dir_expr + "src"
        print(project_dir)

        dir_java_src = bug_info["source_directory"]
        dir_test_src = bug_info["test_directory"]
        f_test_list = bug_info[self.key_failing_test_identifiers]
        p_test_list = bug_info[self.key_passing_test_identifiers]

        print(dir_java_src)
        print(dir_test_src)

        failing_test_identifiers_list = ""
        passing_test_identifiers_list = ""
        for ft in f_test_list:
            if "::" in ft:
                tmp = ft.split("::")[0]
                if tmp not in failing_test_identifiers_list:
                    failing_test_identifiers_list += tmp + ","
            else:
                failing_test_identifiers_list += ft + ","

        for pt in p_test_list:
            print(pt)
            if "::" in pt:
                tmp = pt.split("::")[0]
                if tmp not in passing_test_identifiers_list:
                    passing_test_identifiers_list += tmp + ","
            else:
                passing_test_identifiers_list += pt + ","

        patch_directory = self.dir_output
        setup_scripts = self.dir_setup

        # execute repair tool
        command = (
            f"python3.8 start.py "
            f" {project_dir} "
            f" {dir_java_src} "
            f" {dir_test_src} "
            f" {failing_test_identifiers_list} "
            f" {passing_test_identifiers_list} "
            f" {patch_directory} "
            f" {setup_scripts} "
        )
        timeout_h = str(task_config_info[self.key_timeout])
        repair_command = f"timeout -k 5m {timeout_h}h {command} "

        print(command)

        self.timestamp_log_start()
        status = self.run_command(repair_command, log_file_path=self.log_output_path)
        self.process_status(status)
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        super(APRER, self).save_artifacts(dir_info)

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

        list_output_dir = self.list_dir(self.dir_output + "/generated")
        self.stats.patch_stats.size = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        list_output_dir = self.list_dir(self.dir_output + "/generated")
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        list_output_dir = self.list_dir(self.dir_output + "/candidate")
        self.stats.patch_stats.plausible = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        return self.stats
