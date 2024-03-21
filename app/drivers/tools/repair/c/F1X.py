import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class F1X(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mechtaev/f1x:aprcomp24"
        self.hash_digest = (
            "sha256:3f67b61292222c0b5a96ac01b887e9415f35283b5ca6e9b639be7d68f8bcb6c9"
        )

    def rerun_configuration(self, config_script: str) -> None:
        self.emit_normal("re-running configuration")
        f1x_config_path = self.dir_expr + "/f1x-config"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f"CC=f1x-cc CXX=f1x-cxx {config_script} {self.dir_expr}\n",
            ],
            f1x_config_path,
        )
        reconfig_command = "bash {}".format(f1x_config_path)
        log_reconfig_path = join(self.dir_logs, "f1x-re-config.log")
        self.run_command(reconfig_command, log_file_path=log_reconfig_path)

    def generate_test_driver(self, test_script: str) -> None:
        self.emit_normal(f"preparing test driver for {self.name}")
        test_driver_path = self.dir_expr + "/f1x-test"
        self.write_file(
            [
                "#!/bin/bash\n",
                "bash {1} {0} $@".format(test_script, "-x" if self.is_debug else ""),
            ],
            test_driver_path,
        )
        permission_command = "chmod +x {}".format(test_driver_path)
        self.run_command(permission_command)

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

        config_script = join(self.dir_setup, config_script)
        test_script = join(self.dir_setup, test_script)
        build_script_path = (
            join(self.dir_setup, build_script)
            if not self.is_file(join(self.dir_inst, build_script))
            else join(self.dir_inst, build_script)
        )
        self.rerun_configuration(config_script)
        self.generate_test_driver(test_script)

        if self.is_instrument_only:
            return

        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])

        def process_info(x: Dict[str, Any]) -> str:
            file: str = x.get(self.key_fix_file, "")
            lines = list(map(int, x.get(self.key_fix_lines, [])))
            if not lines:
                return file
            elif len(lines) == 1:
                return file + ":" + str(lines[0])
            else:
                return file + ":" + str(min(lines)) + "-" + str(max(lines))

        fix_file_list = list(
            filter(
                lambda x: x != "",
                map(
                    process_info,
                    bug_info.get(self.key_localization, [{}]),
                ),
            )
        )
        self.emit_debug(fix_file_list)
        passing_test_identifiers_list = bug_info.get(
            self.key_passing_test_identifiers, []
        )
        failing_test_identifiers_list = bug_info.get(
            self.key_failing_test_identifiers, []
        )
        timeout = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        test_driver_path = join(self.dir_expr, "f1x-test")
        test_id_list = ""
        for test_id in failing_test_identifiers_list:
            test_id_list += str(test_id) + " "

        for test_id in passing_test_identifiers_list:
            test_id_list += str(test_id) + " "

        abs_path_buggy_file = None
        if fix_file_list:
            abs_path_buggy_file = ", ".join(
                join(self.dir_expr, "src", f) for f in fix_file_list
            )

        dir_patch = f"{self.dir_output}/patches"
        mkdir_command = "mkdir -p " + dir_patch
        self.run_command(mkdir_command, self.log_output_path, "/")

        self.timestamp_log_start()

        repair_command = "timeout -k 5m {}h f1x ".format(str(timeout))
        if abs_path_buggy_file:
            repair_command += " -f {0} ".format(abs_path_buggy_file)
        repair_command += " -t {0} ".format(test_id_list)
        repair_command += " -T 15000"
        repair_command += " --output-top 5"
        repair_command += " --driver={0} ".format(test_driver_path)
        repair_command += '-b "{0}"'.format(build_script_path)
        if self.is_dump_patches:
            repair_command += " --output-space patch-space "
        if self.is_debug:
            repair_command += " -v "

        dry_command = repair_command + " --disable-dteq"
        dir_src = join(self.dir_expr, "src")
        self.run_command(dry_command, self.log_output_path, dir_src)
        all_command = (
            repair_command
            + " --enable-assignment --disable-dteq --enable-validation  -a -o {}  ".format(
                dir_patch
            )
        )
        if additional_tool_param:
            all_command = all_command + " " + additional_tool_param
        status = self.run_command(all_command, self.log_output_path, dir_src)

        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))

        if self.is_dump_patches:
            for fix_file in fix_file_list:
                self.create_patches_from_space(fix_file)
        self.timestamp_log_end()

    def create_patches_from_space(self, source_file: str) -> None:
        script_name = "{}/{}-dump-patches.py".format(self.dir_expr, self.name)
        abs_path_buggy_file = self.dir_expr + "/src/" + source_file
        dump_command = "timeout -k 5m 1h python3 {} {} {}".format(
            script_name, abs_path_buggy_file, self.dir_expr
        )
        self.run_command(dump_command, self.log_output_path, self.dir_expr)

    def read_log_file(self) -> None:
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "candidates evaluated: " in line:
                    count = (
                        line.split("candidates evaluated: ")[-1]
                        .strip()
                        .replace("\n", "")
                    )
                    if str(count).isnumeric():
                        self.stats.patch_stats.enumerations = int(count)
                elif "validation time: " in line:
                    time = line.split("validation time: ")[-1].strip().replace("\n", "")
                    self.stats.time_stats.total_validation += float(time)
                elif "build time: " in line:
                    time = line.split("build time: ")[-1].strip().replace("\n", "")
                    self.stats.time_stats.total_build += float(time)
                elif "validating patch " in line:
                    self.stats.patch_stats.enumerations += 1
                elif "search space size: " in line:
                    self.stats.patch_stats.size = int(
                        line.split("search space size: ")[-1]
                    )
                elif "plausible patches: " in line:
                    self.stats.patch_stats.plausible = int(
                        line.split("plausible patches: ")[-1]
                    )
                elif "failed to infer compile commands" in line:
                    self.stats.patch_stats.generated = -1
                elif "explored count: 1" in line:
                    if self.stats.time_stats.timestamp_validation == 0:
                        pass

                elif "PASS" in line and "[debug]" in line:
                    if self.stats.time_stats.timestamp_plausible == 0:
                        # self.stats.time_stats.timestamp_plausible = (
                        #     line.split("[debug]")[0].replace("[", "").replace("]", "")
                        # )
                        pass

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

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight("log File: " + self.log_output_path)

        if self.stats.error_stats.is_error:
            self.emit_error("error detected in logs")

        self.read_log_file()

        self.stats.patch_stats.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if self.use_valkyrie else "patches",
                )
            )
        )
        if self.use_valkyrie:
            self.stats.patch_stats.plausible = self.stats.patch_stats.generated

        return self.stats
