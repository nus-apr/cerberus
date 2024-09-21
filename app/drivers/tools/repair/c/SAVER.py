import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import escape_ansi
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SAVER(AbstractRepairTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK",
        "Use After Free": "USE_AFTER_FREE",
        "Double Free": "DOUBLE_FREE",
    }

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "rshariffdeen/saver"
        super().__init__(self.name)

    def populate_config_file(self, bug_info: Dict[str, Any], config_path: str) -> None:
        config_info: Dict[str, Any] = dict()
        bug_type = bug_info[self.key_bug_type]
        if bug_type not in self.bug_conversion_table:
            self.error_exit(f"Unsupported bug type: {bug_type}")

        bug_type_code = self.bug_conversion_table[bug_type]

        if self.key_source not in bug_info:
            self.error_exit(
                f"Missing memory source information in benchmark, required for {self.name}"
            )
        if self.key_sink not in bug_info:
            self.error_exit(
                f"Missing memory sink information in benchmark, required for {self.name}"
            )

        saver_source_info = dict()
        bench_source_info = bug_info[self.key_source]
        if bench_source_info["src-file"]:
            saver_source_info["filename"] = bench_source_info["src-file"]
        saver_source_info["procedure"] = bench_source_info["procedure"]
        saver_source_info["line"] = bench_source_info["line"]
        config_info["source"] = {"node": saver_source_info, "exp": None}

        saver_sink_info = dict()
        bench_sink_info = bug_info[self.key_sink]
        if bench_sink_info["src-file"]:
            saver_sink_info["filename"] = bench_sink_info["src-file"]
        saver_sink_info["procedure"] = bench_sink_info["procedure"]
        saver_sink_info["line"] = bench_sink_info["line"]
        config_info["sink"] = {"node": saver_sink_info, "exp": None}
        config_info["err_type"] = bug_type_code
        self.write_json(config_info, config_path)

    def pre_process(self, bug_info: Dict[str, Any]) -> None:
        self.config_path = None
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        self.emit_normal(" preparing subject for repair with " + self.name)
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)
        config_path = join(self.dir_expr, self.name, "bug.json")
        self.populate_config_file(bug_info, config_path)
        time = datetime.now()
        bug_type = bug_info[self.key_bug_type]
        build_command_repair = bug_info.get(self.key_build_command_repair, "")
        if bug_type == "Memory Leak":
            compile_command = (
                "infer -j 32 -g --headers --check-nullable-only -- {}".format(
                    build_command_repair
                )
            )
        else:
            compile_command = (
                "infer -j 32 run -g --headers --check-nullable-only -- {}".format(
                    build_command_repair
                )
            )
        self.emit_normal(" compiling subject with " + self.name)
        log_compile_path = join(self.dir_logs, "saver-compile-output.log")
        self.run_command(
            compile_command, dir_path=dir_src, log_file_path=log_compile_path
        )
        self.emit_normal(
            " compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        time = datetime.now()
        self.emit_normal(" analysing subject with " + self.name)
        analysis_command = "infer saver --pre-analysis-only "
        log_analysis_path = join(self.dir_logs, "saver-analysis-output.log")
        self.run_command(
            analysis_command, dir_path=dir_src, log_file_path=log_analysis_path
        )
        self.emit_normal(
            " analysis took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

        self.config_path = config_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        config_path = self.config_path
        if self.is_instrument_only:
            return
        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(task_config_info[self.key_timeout])
        subject_name = bug_info[self.key_subject]
        additional_tool_param = task_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-{}-output.log".format(
                task_conf_id, subject_name, self.name.lower(), bug_id
            ),
        )

        self.timestamp_log_start()
        saver_command = "timeout -k 5m {0}h infer saver --error-report {1} ".format(
            str(timeout_h), config_path
        )
        bug_type = bug_info[self.key_bug_type]
        if bug_type in ["Double Free", "Use After Free"]:
            saver_command += " --analysis-with-fimem "
        saver_command += f" {additional_tool_param} "

        dir_src = join(self.dir_expr, "src")
        status = self.run_command(
            saver_command,
            dir_path=dir_src,
            log_file_path=self.log_output_path,
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        # copy_command = "cp -rf {}/src/infer-out {}".format(
        #     self.dir_expr, self.dir_output
        # )
        # self.run_command(copy_command)
        super(SAVER, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
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
        is_error = False

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        count_enumerations = 0
        count_candidates = 0
        for line in log_lines:
            line = escape_ansi(line)
            if "of the total solutions found" in line:
                count_enumerations = int(line.split(": ")[-1])
            elif "opeartion space" in line:
                space_size = line.split(": ")[-1]
                if str(space_size).isnumeric():
                    count_candidates += int(space_size)
            elif "CONVERTING FAILS" in line:
                self.stats.patch_stats.plausible = 0
            elif "ERROR:" in line:
                is_error = True
        if is_error:
            self.emit_error("[error] error detected in logs")

        self.stats.patch_stats.plausible = count_enumerations
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.size = count_candidates
        self.stats.patch_stats.generated = 0
        self.stats.error_stats.is_error = is_error
        return self.stats
