import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SAVER(AbstractRepairTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK",
        "Use After Free": "USE_AFTER_FREE",
        "Double Free": "DOUBLE_FREE",
    }

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)

    def populate_config_file(self, bug_info, config_path):
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

    def prepare(self, bug_info):
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
        if bug_type == "Memory Leak":
            compile_command = (
                "infer -j 20 -g --headers --check-nullable-only -- make -j20"
            )
        else:
            compile_command = (
                "infer -j 20 run -g --headers --check-nullable-only -- make -j20"
            )
        self.emit_normal(" compiling subject with " + self.name)
        self.run_command(compile_command, dir_path=dir_src)
        self.emit_normal(
            " compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        time = datetime.now()
        self.emit_normal(" analysing subject with " + self.name)
        analysis_command = "infer saver --pre-analysis-only "
        self.run_command(analysis_command, dir_path=dir_src)
        self.emit_normal(
            " analysis took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

        return config_path

    def run_repair(self, bug_info, repair_config_info):
        config_path = self.prepare(bug_info)
        super(SAVER, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return
        repair_conf_id = repair_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        if self.use_container:
            self.error_exit(
                "unimplemented functionality: SAVER docker support not implemented"
            )

        self.timestamp_log_start()
        saver_command = "cd {};".format(join(self.dir_expr, "src"))
        saver_command += "timeout -k 5m {0}h saver --error-report {1} ".format(
            str(timeout_h), config_path
        )
        bug_type = bug_info[self.key_bug_type]
        if bug_type in ["Double Free", "Use After Free"]:
            saver_command += " --analysis-with-fimem "
        saver_command += "{0} >> {1} 2>&1 ".format(
            additional_tool_param, self.log_output_path
        )
        status = self.run_command(saver_command)

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        copy_command = "cp -rf {}/saver {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        # infer_output = join(self.dir_expr, "src", "infer-out")
        # copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        # self.run_command(copy_command)
        super(SAVER, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_error = False

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "of the total solutions found" in line:
                count = int(line.split(": ")[-1])
                self._space.plausible = count
                self._space.enumerations = count
            elif "opeartion space" in line:
                space_size = line.split(": ")[-1]
                if str(space_size).isnumeric():
                    self._space.size += int(space_size)
            elif "CONVERTING FAILS" in line:
                self._space.plausible = 0
            elif "ERROR:" in line:
                self._error.is_error = True
        if is_error:
            self.emit_error("[error] error detected in logs")

        return self._space, self._time, self._error
