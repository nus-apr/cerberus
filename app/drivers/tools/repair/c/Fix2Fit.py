import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Fix2Fit(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "yuntongzhang/fix2fit"

    def generate_test_driver(self, test_script: str) -> str:
        self.emit_normal(f"preparing test driver for {self.name}")
        test_driver_path = self.dir_expr + f"/{self.name}-test"
        self.write_file(
            ["#!/bin/bash\n", "bash {0} $@".format(test_script)],
            test_driver_path,
        )
        permission_command = "chmod +x {}".format(test_driver_path)
        self.run_command(permission_command)
        return test_driver_path

    def generate_build_driver(self, build_script: str) -> str:
        self.emit_normal(f"preparing build driver for {self.name}")
        build_driver_path = self.dir_expr + f"/{self.name}-build"
        self.write_file(
            [
                "#!/bin/bash\n",
                f"CC=f1x-cc CXX=f1x-cxx {build_script}\n",
            ],
            build_driver_path,
        )
        permission_command = "chmod +x {}".format(build_driver_path)
        self.run_command(permission_command)
        return build_driver_path

    def generate_config_driver(self, config_script: str) -> str:
        self.emit_normal(f"preparing config driver for {self.name}")
        config_driver_path = self.dir_expr + f"/{self.name}-config"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"CC=f1x-cc CXX=f1x-cxx {config_script} {self.dir_expr}\n",
            ],
            config_driver_path,
        )
        permission_command = "chmod +x {}".format(config_driver_path)
        self.run_command(permission_command)
        return config_driver_path

    def clean_subject(self) -> None:
        self.emit_normal(f"cleaning previous artifacts")
        clean_script = self.dir_expr + f"{self.name}-clean"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                'find . -name "*.cache" | xargs rm -rf\n',
            ],
            clean_script,
        )
        clean_command = "bash {}".format(clean_script)
        log_clean_path = join(self.dir_logs, f"{self.name}-clean.log")
        self.run_command(clean_command, log_file_path=log_clean_path)

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        config_script = bug_info.get(self.key_config_script, None)
        build_script = bug_info.get(self.key_build_script, None)
        test_script = bug_info.get(self.key_test_script, None)

        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")
        if not test_script:
            self.error_exit(f"{self.name} requires a test script as input")

        config_script_path = join(self.dir_setup, config_script)
        test_script_path = join(self.dir_setup, test_script)
        build_script_path = join(self.dir_setup, build_script)

        config_driver = self.generate_config_driver(config_script_path)
        build_driver = self.generate_build_driver(build_script_path)
        test_driver = self.generate_test_driver(test_script_path)
        self.clean_subject()

        if self.is_instrument_only:
            return
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        fix_location = bug_info[self.key_localization][0][self.key_fix_file]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        abs_path_binary = join(self.dir_expr, "src", bug_info[self.key_bin_path])
        passing_test_identifiers_list = bug_info[self.key_passing_test_identifiers]
        failing_test_identifiers_list = bug_info[self.key_failing_test_identifiers]
        test_id_list = ""
        for test_id in failing_test_identifiers_list:
            test_id_list += test_id + " "
        if passing_test_identifiers_list:
            for test_id in passing_test_identifiers_list:
                test_id_list += test_id + " "

        abs_path_buggy_file = join(
            self.dir_expr,
            "src",
            (
                fix_location
                if fix_location
                else self.read_file(self.dir_expr + "/manifest.txt")[0]
            ),
        )

        self.timestamp_log_start()
        if self.key_crash_cmd not in bug_info:
            self.error_exit("No Crash command provided")
        environment_vars = {
            "SUBJECT_DIR": self.dir_expr,
            "AFL_NO_AFFINITY": "",
            "BUGGY_FILE": abs_path_buggy_file,
            "TESTCASE": test_id_list,
            "CONFIG": config_driver,
            "BUILD": build_driver,
            "DRIVER": test_driver,
            "BINARY": abs_path_binary,
            "T_TIMEOUT": "{}000".format(task_config_info[self.key_config_timeout_test]),
            "TIMEOUT": "{}h; ".format(task_config_info[self.key_timeout]),
            "BINARY_INPUT": bug_info[self.key_crash_cmd],
        }

        repair_command = "timeout -k 5m {}h bash /src/scripts/run.sh ".format(
            str(task_config_info[self.key_timeout])
        )
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_expr, env=environment_vars
        )

        self.process_status(status)
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        dir_patch = join(self.dir_expr, "patches")
        self.run_command("mkdir {}".format(self.dir_output))
        self.run_command("cp -rf {} {}/patches".format(dir_patch, self.dir_output))
        super(Fix2Fit, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        count_filtered = 0

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)

        is_timeout = True
        reported_failing_test_identifiers = []
        if self.is_file(dir_results + "/original.txt"):
            log_lines = self.read_file(dir_results + "/original.txt")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "no patch found" in line:
                    self.emit_warning("[warning] no patch found by F1X")
                elif "negative tests: [" in line:
                    reported_failing_test_identifiers = (
                        str(line)
                        .split("negative tests: [")[-1]
                        .split("]")[0]
                        .split(", ")
                    )
                elif "search space size: " in line:
                    self.stats.patch_stats.size = int(
                        line.split("search space size: ")[-1].strip()
                    )

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "search space size: " in line:
                self.stats.patch_stats.size = int(
                    line.split("search space size: ")[-1].strip()
                )
            elif "candidates evaluated: " in line:
                self.stats.patch_stats.enumerations = int(
                    line.split("candidates evaluated: ")[-1].strip()
                )
            elif "exploration progress: " in line:
                self.stats.patch_stats.enumerations = int(
                    int(
                        line.split("exploration progress: ")[-1]
                        .strip()
                        .replace("%", "")
                    )
                    / 100
                    * self.stats.patch_stats.size
                )
            elif "plausible patches: " in line:
                self.stats.patch_stats.plausible = int(
                    line.split("plausible patches: ")[-1].strip()
                )
            elif "partition size: " in line:
                self.stats.patch_stats.plausible = (
                    int(line.split("partition size: ")[-1].strip())
                    + self.stats.patch_stats.plausible
                )
            elif "patches successfully generated" in line:
                is_timeout = False
            elif "no patch found" in line:
                is_timeout = False
            elif "Fail to execute f1x" in line:
                self.stats.error_stats.is_error = True
            elif "tests are not specified" in line:
                self.stats.error_stats.is_error = True
                self.emit_warning("[warning] no tests provided")
            elif "no negative tests" in line:
                self.emit_warning("[warning] no negative tests")
            elif "failed to infer compile commands" in line:
                self.stats.error_stats.is_error = True
                self.emit_error("[error] compilation command not found")
            elif "At-risk data found" in line:
                self.stats.error_stats.is_error = True
                self.emit_error("[error] previous results have corrupted")

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout detected")
        if (
            reported_failing_test_identifiers != fail_list
            and reported_failing_test_identifiers
            and not is_timeout
        ):
            self.emit_warning("[warning] unexpected failing test-cases reported")
            self.emit_warning("expected fail list: {0}".format(",".join(fail_list)))
            self.emit_warning(
                "reported fail list: {0}".format(
                    ",".join(reported_failing_test_identifiers)
                )
            )

        dir_patch = self.dir_expr + "/patches"
        self.stats.patch_stats.generated = len(self.list_dir(dir_patch))
        return self.stats
