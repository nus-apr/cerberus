import os
from os import path
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class ExtractFix(AbstractRepairTool):
    bug_conversion_table = {
        "Buffer Overflow": "buffer_overflow",
        "Use after Free": "buffer_overflow",
        "Integer Overflow": "integer_overflow",
        "Data Type Overflow": "integer_overflow",
        "Null Pointer Dereference": "null_pointer",
        "Divide by Zero": "divide_by_0",
        "API Assertion": "assertion_failure",
        "API Specific": "api_specific",
    }

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.dir_root = "/ExtractFix/"
        self.image_name = "gaoxiang9430/extractfix:demo"

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

        # modify the output directory as it depends on the experiment
        self.dir_output = path.join(self.dir_expr, "result")
        self.dir_logs = path.join(self.dir_expr, "logs")

        dir_extractfix_exist = self.is_dir(self.dir_root)
        if not dir_extractfix_exist:
            # self.emit_error(
            #     "[Exception] ExtractFix repo is not at the expected location. "
            #     "Please double check whether we are in ExtractFix container."
            # )
            self.error_exit("ExtractFix repo is not at the expected location.")
        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        # prepare the config file
        parameters = self.create_parameters(bug_info)

        # start running
        self.timestamp_log_start()
        extractfix_command = "bash -c 'source /ExtractFix/setup.sh && timeout -k 5m {}h ./ExtractFix.py {} {} >> {}'".format(
            timeout_h, parameters, additional_tool_param, self.log_output_path
        )
        status = self.run_command(
            extractfix_command,
            log_file_path=self.log_output_path,
            dir_path=path.join(self.dir_root, "build"),
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def create_parameters(self, experiment_info: Dict[str, Any]) -> str:
        """
        Construct the parametes for ExtractFix.
        """

        # (1) source-dir
        line_source_dir = "-s " + (
            "/libtiff-3186"
            if experiment_info[self.key_bug_id] == "CVE-2016-3186"
            else (
                "/coreutils-25003"
                if experiment_info[self.key_bug_id] == "gnubug-25003"
                else self.dir_expr
            )
        )

        # (2) test file
        # dir_tests = "/".join([self.dir_setup, "tests"])
        # tests_list = self.list_dir(dir_tests)
        # if not tests_list:
        #     self.emit_error(
        #         "[Exception] there needs to be at least 1 exploit (failing) input!"
        #     )
        #     error_exit("Unhandled Exception")
        # Currently we assume that the test cases are copied, this can be simplified by using the tests_lsit above
        test_case = "-t " + (
            experiment_info[self.key_exploit_list][0]
            if len(experiment_info[self.key_exploit_list]) != 0
            else "dummy"
        )

        # (3) driver
        driver = "-c driver"

        # (4) bug type
        bug_type = "-b " + (
            "api_specific"
            if experiment_info[self.key_bug_id] == "CVE-2016-3186"
            or experiment_info[self.key_bug_id] == "gnubug-25003"
            else ExtractFix.bug_conversion_table.get(
                experiment_info[self.key_bug_type], ""
            )
        )

        if bug_type == "-b ":
            self.error_exit(
                "Bug {} does not have {} field to indicate the type".format(
                    experiment_info[self.key_bug_id], self.key_bug_type
                )
            )

        # (5) buggy program
        program = "-n " + experiment_info[self.key_bin_path].split("/")[-1]

        # (6) verbose?
        verbose = "-v"

        return " ".join(
            [line_source_dir, test_case, driver, bug_type, program, verbose]
        )

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        self.run_command(
            "cp -r result0 result/", dir_path=path.join(self.dir_root, self.dir_expr)
        )
        self.run_command(
            "cp -r result1 result/", dir_path=path.join(self.dir_root, self.dir_expr)
        )
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
            [name for name in list_output_dir if "patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "successfully generate patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.error_stats.is_error = is_error
        return self.stats
