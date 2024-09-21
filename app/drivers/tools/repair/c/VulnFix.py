import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class VulnFix(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.dir_root = "/home/yuntong/vulnfix"
        self.image_name = "yuntongzhang/vulnfix:latest-manual"
        self.cpu_usage = 1

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """
        if self.is_instrument_only:
            return

        dir_vulnfix_exist = self.is_dir(self.dir_root)
        if not dir_vulnfix_exist:
            # self.emit_error(
            #     "[Exception] Vulnfix repo is not at the expected location. "
            #     "Please double check whether we are in VulnFix container."
            # )
            self.error_exit("vulnfix repo is not at the expected location")
        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        # get ready the config file
        config_path = self.populate_config_file(bug_info)

        # start running
        self.timestamp_log_start()
        vulnfix_command = "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h vulnfix {1} {2}'".format(
            timeout_h, additional_tool_param, config_path
        )
        env = dict()
        env["AFL_NO_AFFINITY"] = str(1)
        status = self.run_command(
            vulnfix_command,
            log_file_path=self.log_output_path,
            dir_path=self.dir_root,
            env=env,
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def populate_config_file(self, bug_info: Dict[str, Any]) -> str:
        """
        Some fields of the VulnFix config file contains information which overlaps with what
        Cerberus already has, and also some of the fields depends on actual paths in the system. These fields are populated here into the existing config file template.
        """
        # the config template should have been copied here
        config_path = join(self.dir_expr, "vulnfix", "config")

        # first check whether config already has a cmd line;
        # this is because vulnfix sometimes instrument program for AFL argv fuzzing, which
        # changes the command for invoking the program
        orig_config_lines = self.read_file(config_path)
        cmd_already_specified = False
        binary_already_specified = False
        for config_line in orig_config_lines:
            config_type = config_line.split("=")[0]
            if config_type == "cmd":
                cmd_already_specified = True
            if config_type == "binary":
                binary_already_specified = True

        # (1) source-dir
        dir_src = join(self.dir_expr, "src")
        line_source_dir = "source-dir=" + dir_src + "\n"
        # (2) binary
        rel_binary_path = bug_info[self.key_bin_path]
        binary_path = join(dir_src, rel_binary_path)
        line_binary = "binary=" + binary_path + "\n"
        # (3) (OPTIONAL) cmd
        line_cmd = ""
        if not cmd_already_specified:
            if self.key_crash_cmd not in bug_info:
                self.error_exit("No Crash command provided")
            cmd = bug_info[self.key_crash_cmd]
            cmd = cmd.replace("$POC", "<exploit>")
            line_cmd = "cmd=" + cmd + "\n"

        fix_info = bug_info[self.key_localization][0]

        fix_file_path = fix_info[self.key_fix_file]
        fix_line = fix_info[self.key_fix_lines][0]
        crash_file = bug_info["stack_trace"][0]["source_file"]
        crash_file = os.path.basename(crash_file)
        crash_line = bug_info["stack_trace"][0]["line"]
        crash_location = f"{crash_file}:{crash_line}"

        fix_location = f"{os.path.basename(fix_file_path)}:{fix_line}"

        all_cmds = f"fix-file-path={fix_file_path}\nfix-line={fix_line}\ncrash-location={crash_location}\nfix-location={fix_location}"

        # (4) exploit
        self.emit_debug(bug_info)
        if (
            self.key_failing_test_identifiers not in bug_info
            or len(bug_info[self.key_failing_test_identifiers]) < 1
        ):
            # assumes instrumentation converted stdarg as a file handling command
            exploit_path = join(self.dir_setup, "tests/exploit")
        else:
            self.emit_debug(bug_info)
            self.emit_debug(bug_info[self.key_failing_test_identifiers])

            exploit_path = join(
                self.dir_setup,
                "tests",
                sorted(bug_info[self.key_failing_test_identifiers])[0],
            )
        line_exploit = "exploit=" + exploit_path + "\n"
        # (5) (OPTIONAL) normal-in
        line_normals = ""
        dir_normal_in = join(self.dir_setup, "vulnfix", "normals")
        normals_list = self.list_dir(dir_normal_in)
        if normals_list:
            line_normals = "normal-in=" + ",".join(normals_list) + "\n"

        # (6) runtime-dir
        line_runtime_dir = "runtime-dir=" + self.dir_output + "\n"

        self.run_command("mkdir -p {}/afl-out/crashes".format(self.dir_output))

        config_updates = list()
        if not binary_already_specified:
            config_updates.append(line_binary)
        if line_cmd:
            config_updates.append(line_cmd)
        config_updates.append(line_exploit)
        if line_normals:
            config_updates.append(line_normals)
        config_updates.append(line_runtime_dir)
        config_updates.append(line_source_dir)
        config_updates.append(all_cmds)
        self.append_file(config_updates, config_path)
        return config_path

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)
        return

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

        is_error = False
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
                if "Generating patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.error_stats.is_error = is_error
        return self.stats
