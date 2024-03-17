import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import escape_ansi
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class FuzzRepair(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/fuzzrepair:tool"
        self.bug_id = ""

    def transform_source(self, source_file_list: Optional[List[str]]) -> None:
        self.emit_normal("applying transformations for source files")
        script_path = self.dir_expr + f"/{self.name}-transform"
        if not source_file_list:
            return
        source_list_str = " ".join([f"'{s}'" for s in source_file_list])
        self.write_file(
            [
                "#!/bin/bash\n",
                f"file_list=({source_list_str})\n",
                f"cd $LIBPATCH_DIR/rewriter\n",
                'for t in "${file_list[@]}"\n',
                "do\n",
                "./rewritecond $t -o $t\n",
                "ret=$?\n",
                "if [[ ret -eq 1 ]]\n",
                "then\n",
                "exit 128\n",
                "fi\n" "done\n",
            ],
            script_path,
        )
        reconfig_command = "bash {}".format(script_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-transform.log")
        status = self.run_command(reconfig_command, log_file_path=log_reconfig_path)
        if status != 0:
            self.error_exit("transforming subject failed")

    def rerun_configuration(
        self, config_script: str, build_script: str, cc: str, cxx: str
    ) -> None:
        self.emit_normal("re-building subject with fuzzrepair compilers")
        script_path = self.dir_expr + f"/{self.name}-rebuild"
        dir_src = join(self.dir_expr, "src")
        content_list = [
            "#!/bin/bash\n",
            f"cd {dir_src}\n",
            "make distclean; rm -f CMakeCache.txt\n",
            f"CC={cc} CXX={cxx} {config_script} {self.dir_base_expr}\n",
            f"cd {dir_src}\n",
        ]

        if cc == "fuzzrepair-cc":
            content_list.append(
                f'CC={cc} CXX={cxx} CFLAGS="-Wno-error -fPIC" CPPFLAGS=$CFLAGS CXXFLAGS=$CFLAGS {build_script} {self.dir_base_expr}\n'
            )
        else:
            content_list.append(
                f"CC={cc} CXX={cxx} bear {build_script} {self.dir_base_expr}\n"
            )
        content_list.append('sed -i "s/-I/-isystem/g" compile_commands.json\n')
        self.write_file(content_list, script_path)
        reconfig_command = "bash {}".format(script_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-re-build.log")
        status = self.run_command(reconfig_command, log_file_path=log_reconfig_path)
        if status != 0:
            self.error_exit("rebuilding subject failed")

    def generate_conf_file(self, bug_info: Dict[str, Any]) -> str:
        repair_conf_path = join(self.dir_setup, "fuzzrepair.conf")
        conf_content = []
        # check there is a file-input defined, if not use default exploit command
        # for example coreutils in vulnloc/extractfix benchmarks have stdarg which are not file inputs
        # instrumentation should convert such to a file argument
        exploit_file_list = bug_info.get(self.key_exploit_list, None)
        if exploit_file_list:
            poc_list = bug_info[self.key_exploit_list]
            crash_cmd = bug_info[self.key_crash_cmd]
        else:
            poc_list = ["tests/exploit"]
            crash_cmd = ""

        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]
        self.bug_id = bug_info[self.key_bug_id]
        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[self.key_bug_id]))
        conf_content.append("binary_path:src/{}\n".format(bug_info[self.key_bin_path]))

        conf_content.append("exploit_command:{}\n".format(crash_cmd))
        conf_content.append(
            "fix_file:{}\n".format(
                bug_info[self.key_localization][0][self.key_fix_file]
            ).replace("//", "/")
        )
        conf_content.append("poc:{}\n".format(poc_abs_list[0]))

        # TODO: temp way of only using crash oracle on some bugs
        if "libtiff" in self.dir_expr:
            conf_content.append("only_crash_oracle:1\n")

        self.write_file(conf_content, repair_conf_path)
        return repair_conf_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        config_script = bug_info.get(self.key_config_script, None)
        build_script = bug_info.get(self.key_build_script, None)

        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")

        config_script_path = join(self.dir_setup, config_script)
        build_script_path = join(self.dir_setup, build_script)
        fix_file = bug_info[self.key_localization][0][self.key_fix_file]
        dir_src = join(self.dir_expr, "src")
        transform_file_list = []
        if isinstance(fix_file, list):
            transform_file_list = [f"{dir_src}/{f}" for f in fix_file]
        elif isinstance(fix_file, str):
            transform_file_list = [f"{dir_src}/{fix_file}"]
        else:
            self.error_exit("fix file is not a list or string")

        if not bug_info[self.key_benchmark] == "vulnloc":
            self.rerun_configuration(
                config_script_path, build_script_path, "clang", "clang++"
            )
            self.transform_source(transform_file_list)
            self.rerun_configuration(
                config_script_path, build_script_path, "fuzzrepair-cc", "fuzzrepair-cxx"
            )

        timeout_h = str(task_config_info[self.key_timeout])
        timeout_m = str(int(float(timeout_h) * 60))
        additional_tool_param = task_config_info[self.key_tool_params]
        repair_conf_path = self.generate_conf_file(bug_info)
        self.emit_normal(f"running {self.name}")
        self.timestamp_log_start()
        repair_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h ".format(
                str(timeout_h)
            )
        )
        repair_command += " fuzzrepair --conf={0} --time-duration={1} {2}'".format(
            repair_conf_path, str(timeout_m), additional_tool_param
        )

        status = self.run_command(repair_command, log_file_path=self.log_output_path)

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        tool_log_dir = "/FuzzRepair/logs/"
        copy_command = "cp -rf {} {}".format(tool_log_dir, self.dir_output)
        self.run_command(copy_command)
        tool_artifact_dir = "/FuzzRepair/output/{}".format(self.bug_id)
        copy_command = "cp -rf {} {}".format(tool_artifact_dir, self.dir_output)
        self.run_command(copy_command)
        super(FuzzRepair, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        json_report = join(self.dir_output, self.bug_id, "final-result")
        dir_patch = join(self.dir_output, self.bug_id, "plausible-patches")
        list_patches = self.list_dir(dir_patch, regex="*.patch")
        count_enumerations = 0
        count_over_fitting = 0
        count_invalid = 0
        space_size = 0
        self.stats.patch_stats.generated = len(list_patches)
        is_error = False

        self.emit_normal("reading stdout log")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = escape_ansi(log_lines[0].strip())
        self.stats.time_stats.timestamp_end = escape_ansi(log_lines[-1].strip())
        if self.is_file(json_report):
            self.emit_normal("reading result.json")
            result_info = self.read_json(json_report, encoding="iso-8859-1")
            if result_info:
                count_enumerations = int(
                    result_info["agg-stats"]["patch-fuzzing-num-new-unique-patches"]
                )
                count_invalid = int(
                    result_info["agg-stats"]["prune-stage-num-invalid-patches"]
                )
                count_over_fitting = int(
                    result_info["agg-stats"]["prune-stage-num-pruned-total"]
                )

        else:
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "patch-fuzzing-num-new-unique-patches" in line:
                    parsed_info = re.search(r"\', (.*?)\)", line)
                    if parsed_info:
                        count_enumerations = int(parsed_info.group(1))
                elif "prune-stage-num-invalid-patches" in line:
                    parsed_info = re.search(r"\', (.*?)\)", line)
                    if parsed_info:
                        count_invalid = int(parsed_info.group(1))
                elif "prune-stage-num-pruned-total" in line:
                    parsed_info = re.search(r"\', (.*?)\)", line)
                    if parsed_info:
                        count_over_fitting = int(parsed_info.group(1))
            if is_error:
                self.emit_error("[error] error detected in logs")

        count_plausible = count_enumerations - count_over_fitting - count_invalid
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.non_compilable = count_invalid
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.size = space_size
        self.stats.error_stats.is_error = is_error

        return self.stats
