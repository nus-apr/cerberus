import os
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class CrashRepair(AbstractLocalizeTool):
    error_messages = ["aborted", "core dumped", "runtime error", "segmentation fault"]

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/crashrepair:tool"

    def instrument(self, bug_info: Dict[str, Any]) -> None:
        """instrumentation for the experiment as needed by the tool"""
        self.emit_normal("Running dynamic instrumentation")
        bug_id = bug_info[self.key_bug_id]
        dir_src = join(self.dir_expr, "src")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(task_conf_id, self.name, bug_id),
        )
        inst_script_path = self.dir_expr + f"/{self.name}-instrument"
        content = []
        for func_name in ["rint", "fabs", "longjmp"]:
            content.append(
                'grep -nrl -e "{0}" | grep "\.c" | '
                "xargs -I @ sed -i "
                "-e 's/ {0}(/ {0}_crepair(/g' "
                "-e 's/\t{0}(/\t{0}_crepair(/g'"
                " @\n".format(func_name)
            )
            content.append(
                'grep -nrl -e "{0}_crepair" | grep "\.c" | xargs git add \n'.format(
                    func_name
                )
            )

        content.append('git config --global user.email "you@example.com"\n')
        content.append('git config --global user.name "Your Name"\n')
        content.append("git commit -m 'replace with proxy functions'")
        self.write_file(content, inst_script_path)
        reconfig_command = "bash {}".format(inst_script_path)
        self.run_command(
            reconfig_command, log_file_path=self.log_instrument_path, dir_path=dir_src
        )
        time = datetime.now()
        self.emit_debug(
            "\t\t\t instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return

    def rerun_configuration(self, config_script: str, build_script: str) -> None:
        self.emit_normal("re-running configuration and build")
        _config_path = self.dir_expr + f"/{self.name}-config-build"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f"CC=crepair-cc CXX=crepair-cxx {config_script} {self.dir_expr}\n",
                f"CC=crepair-cc CXX=crepair-cxx {build_script} {self.dir_expr}\n",
            ],
            _config_path,
        )
        reconfig_command = "bash {}".format(_config_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-re-config-build.log")
        self.run_command(reconfig_command, log_file_path=log_reconfig_path)

    def generate_conf_file(self, bug_info: Dict[str, Any]) -> str:
        repair_conf_path = join(self.dir_expr, "crashrepair.conf")
        conf_content = []
        if self.key_exploit_list not in bug_info:
            self.error_exit("CrashRepair requires a proof of concept")
        poc_list = bug_info[self.key_exploit_list]
        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]
        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[self.key_bug_id]))
        conf_content.append("src_directory:src\n")
        conf_content.append("binary_path:{}\n".format(bug_info[self.key_bin_path]))
        conf_content.append("config_command:skip\n")
        conf_content.append("build_command:skip\n")
        if self.key_crash_cmd not in bug_info:
            self.error_exit("CrashRepair requires a test input list")

        conf_content.append("test_input_list:{}\n".format(bug_info[self.key_crash_cmd]))
        conf_content.append("poc_list:{}\n".format(",".join(poc_abs_list)))
        conf_content.append(
            "klee_flags:--link-llvm-lib=/CrashRepair/lib/libjpeg-8.4.bca "
            "--link-llvm-lib=/CrashRepair/lib/libz.bca "
            "--link-llvm-lib=/CrashRepair/lib/liblzma.bca "
            "--link-llvm-lib=/CrashRepair/lib/libjbig.bca "
            "--link-llvm-lib=/CrashRepair/lib/libcrepair_proxy.bca\n"
        )
        self.append_file(conf_content, repair_conf_path)
        return repair_conf_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        conf_path = self.generate_conf_file(bug_info)
        config_script = bug_info.get(self.key_config_script, None)
        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        build_script = bug_info.get(self.key_build_script, None)
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")

        config_script = join(self.dir_setup, config_script)
        build_script = join(self.dir_setup, build_script)
        self.rerun_configuration(config_script, build_script)
        timeout_h = str(task_config_info[self.key_timeout])
        timeout_m = 60 * float(timeout_h)
        timeout_validation = int(timeout_m * 0.75)
        timeout_test = 30
        additional_tool_param = task_config_info[self.key_tool_params]
        patch_limit = 10
        bug_json_path = self.dir_expr + "/bug.json"
        self.timestamp_log_start()
        self.emit_normal(f"running {self.name}")
        repair_command = (
            f"bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {str(timeout_h)}h "
            f"crepair --conf={conf_path} "
            f" {additional_tool_param} '"
        )

        status = self.run_command(repair_command, log_file_path=self.log_output_path)
        if status >= 0:
            status = 0
        self.process_status(status)
        self.timestamp_log_end()
        result_file = f"/CrashRepair/output/{bug_info[self.key_bug_id]}/analysis.json"
        if self.is_file(result_file):
            analysis_info = self.read_json(result_file)
            if not isinstance(analysis_info, Dict):
                self.error_exit("expected analysis info to be a dictionary")
            localization_list = analysis_info["analysis_output"][0]["localization"]
            processed_loc_info = list()
            loc_list = list()
            for _l in localization_list:
                abs_file_path = _l[self.key_fix_file]
                line_num = _l[self.key_fix_lines]
                src_loc = f"{abs_file_path}:{line_num}"
                if src_loc in loc_list:
                    continue
                loc_list.append(src_loc)
                rel_file_path = abs_file_path.replace(self.dir_expr + "src/", "")
                _l[self.key_fix_file] = rel_file_path

                processed_loc_info.append(_l)
            new_metadata = {
                "generator": self.name,
                "confidence": 1,
                "localization": processed_loc_info,
            }

            self.write_json(
                [{self.key_analysis_output: [new_metadata]}],
                join(self.dir_output, "meta-data.json"),
            )

        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        list_artifact_dirs = ["/CrashRepair/output/", "/CrashRepair/logs/"]
        list_artifact_files = [
            f"/CrashRepair/output/{self.stats.bug_info[self.key_bug_id]}/analysis.json"
        ]
        for d in list_artifact_dirs:
            copy_command = f"cp -rf {d} {self.dir_output}"
            self.run_command(copy_command)
        for f in list_artifact_files:
            copy_command = f"cp {f} {self.dir_output}"
            self.run_command(copy_command)
        super(CrashRepair, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        self.emit_normal("reading output")
        report_path = f"/CrashRepair/output/{bug_id}/analysis.json"
        report_json = self.read_json(report_path)

        count_fix_locs = 0
        count_src_files = 0
        count_fix_funcs = 0
        if report_json:
            localization_list = report_json.get("analysis_output")[0].get(
                "localization"
            )
            if localization_list:
                count_fix_locs = len(localization_list)
                src_files = set()
                fix_funcs = set()
                for l in localization_list:
                    src_files.add(l.get("source_file"))
                    fix_funcs.add(l.get("function"))
                count_fix_funcs = len(fix_funcs)
                count_src_files = len(src_files)

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
                if any(err in line.lower() for err in self.error_messages):
                    self.stats.error_stats.is_error = True

        self.stats.fix_loc_stats.fix_locs = count_fix_locs
        self.stats.fix_loc_stats.source_files = count_src_files
        self.stats.fix_loc_stats.fix_funcs = count_fix_funcs
        return self.stats
