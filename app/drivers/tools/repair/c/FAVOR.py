import os
import re
import subprocess
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class FAVOR(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.dir_root = "/FAVOR/"
        self.image_name = "dongqa/favor:latest"
        self.hash_digest = (
            "sha256:765ba38e429af4cc75e39d70ead10837697321bea2dbb36c3b14be88184a4b93"
        )

    def prepare_for_repair(
        self,
        buggy_filepath: str,
        buggy_loc: int,
        test_case_path: str,
        binary_path: str,
        crash_command: str,
    ) -> None:
        # removing comments from source file and extracting the buggy function execute path
        # buggy_loc_strs = " ".join(map(str, buggy_loc))
        buggy_loc_command = f"--bug_loc 0"
        buggy_filepath_command = f"--buggy_filepath {buggy_filepath}"
        binary_path_command = f"--binary_path {binary_path}"
        test_case_path_command = f"--test_case_path {test_case_path}"
        crash_command = f'--crash_command "{crash_command}" '
        self.emit_normal("prepare for repair phase")
        prepare_command = (
            "bash -c 'source /root/anaconda3/etc/profile.d/conda.sh && "
            "conda activate favor && cd {} && python3 preparing.py {} {} {} {} {}>> {}'".format(
                self.dir_root,
                buggy_filepath_command,
                buggy_loc_command,
                test_case_path_command,
                binary_path_command,
                crash_command,
                self.log_output_path,
            )
        )
        status = self.run_command(
            prepare_command, log_file_path=self.log_output_path, dir_path=self.dir_root
        )
        self.process_status(status)

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        buggy_loc = bug_info.get("line_numbers", None)
        test_case = bug_info.get("exploit_file_list", [])
        if not test_case:
            self.emit_error("No test cases provided for the bug")
        source_file = bug_info.get("source_file", None)
        if not source_file:
            self.emit_error("No source file provided for the bug")
        binary_path = bug_info.get("binary_path", None)
        if not binary_path:
            self.emit_error("No binary path provided for the bug")
        config_script = bug_info.get("config_script", None)
        if not config_script:
            self.emit_error("No config script provided for the bug")
        build_script = bug_info.get("build_script", None)
        if not build_script:
            self.emit_error("No build script provided for the bug")
        crash_command = bug_info.get("crash_cmd", None)
        if not crash_command:
            self.emit_error("No crash command provided for the bug")

        test_case_path = os.path.join(self.dir_setup, test_case[0])
        buggy_file_path = os.path.join(self.dir_expr, f"src", source_file)
        binary_path = os.path.join(self.dir_expr, f"src", binary_path)
        crash_command = crash_command.replace("$POC", test_case_path)

        if not self.is_file(buggy_file_path):
            self.error_exit("buggy source file not found")

        if buggy_loc is None:
            # if buggy_loc is not provided, favor will employ another vulnerability localization tool to get relevant locs.
            buggy_loc = 0

        clean_script = os.path.join(self.dir_setup, f"clean_subject")
        config_script = os.path.join(self.dir_setup, config_script)
        build_script = os.path.join(self.dir_setup, build_script)

        self.run_command(
            clean_script, log_file_path=self.log_output_path, dir_path=self.dir_root
        )
        self.run_command(
            config_script, log_file_path=self.log_output_path, dir_path=self.dir_root
        )
        self.run_command(
            build_script, log_file_path=self.log_output_path, dir_path=self.dir_root
        )

        self.prepare_for_repair(
            buggy_file_path, buggy_loc, test_case_path, binary_path, crash_command
        )
        self.timestamp_log_start()
        self.emit_normal("running repair phase")
        timeout_h = str(task_config_info[self.key_timeout])
        favor_command = (
            "bash -c 'source /root/anaconda3/etc/profile.d/conda.sh && cd {} && conda activate favor "
            "&& timeout -k 5m {}h sh ./favor.sh >> {}'".format(
                self.dir_root, timeout_h, self.log_output_path
            )
        )

        status = self.run_command(
            favor_command,
            log_file_path=self.log_output_path,
            dir_path=self.dir_root,
        )
        self.process_status(status)
        self.emit_normal("generate patches")
        generate_command = (
            f"python3 generate_patch.py --buggy_filepath {buggy_file_path}"
        )
        status = self.run_command(
            generate_command, log_file_path=self.log_output_path, dir_path=self.dir_root
        )
        self.process_status(status)
        # patch_dir = join(self.dir_output, "patches")
        # self.run_command("mkdir {}".format(patch_dir))
        copy_command = "cp -r /FAVOR/patches/ {}".format(self.dir_output)
        status = self.run_command(copy_command)
        self.process_status(status)
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        # self.emit_normal("prepare for repairing phase")
        # buggy_file_path = os.path.join(self.dir_expr, f'src', bug_info.get('source_file'))
        # generate_command = f"python3 generate_patch.py --buggy_filepath {buggy_file_path}"
        # status = self.run_command(
        #     generate_command, log_file_path=self.log_output_path, dir_path=self.dir_root
        # )
        # self.process_status(status)
        # patch_dir = join(self.dir_output, "patches")
        # self.run_command("mkdir {}".format(patch_dir))
        # copy_command = "cp  {}patches/*.patch {}".format(self.dir_root, patch_dir)
        # status = self.run_command(
        #     copy_command, log_file_path=self.log_output_path, dir_path=self.dir_root
        # )
        # self.process_status(status)
        super(FAVOR, self).save_artifacts(dir_info)

    # def analyse_output(self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]):
    #     """
    #     analyse tool output and collect information
    #     output of the tool is logged at self.log_output_path
    #     information required to be extracted are:
    #
    #         self.stats.patches_stats.non_compilable
    #         self.stats.patches_stats.plausible
    #         self.stats.patches_stats.size
    #         self.stats.patches_stats.enumerations
    #         self.stats.patches_stats.generated
    #
    #         self.stats.time_stats.total_validation
    #         self.stats.time_stats.total_build
    #         self.stats.time_stats.timestamp_compilation
    #         self.stats.time_stats.timestamp_validation
    #         self.stats.time_stats.timestamp_plausible
    #     """
    #     self.emit_normal("reading output")
    #
    #     is_error = False
    #     count_plausible = 0
    #     count_enumerations = 0
    #
    #     # count number of patch files
    #     list_output_dir = self.list_dir(self.dir_output)
    #     self.stats.patch_stats.generated = len(
    #         [name for name in list_output_dir if ".patch" in name]
    #     )
    #
    #     # extract information from output log
    #     if not self.log_output_path or not self.is_file(self.log_output_path):
    #         self.emit_warning("no output log file found")
    #         return self.stats
    #
    #     self.emit_highlight(f"output log file: {self.log_output_path}")
    #     if self.is_file(self.log_output_path):
    #         log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
    #         self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
    #         self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
    #
    #         for line in log_lines:
    #             if "Generating patch" in line:
    #                 count_plausible += 1
    #                 count_enumerations += 1
    #
    #     self.stats.patch_stats.plausible = count_plausible
    #     self.stats.patch_stats.enumerations = count_enumerations
    #     self.stats.error_stats.is_error = is_error
    #     return self.stats
