import os
import re
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.core.utilities import execute_command
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
        super(SAVER, self).__init__(self.name)

    def populate_config_file(self, bug_info, config_path):
        config_info: Dict[str, Any] = dict()
        bug_type = bug_info[definitions.KEY_BUG_TYPE]
        if bug_type not in self.bug_conversion_table:
            error_exit(f"Unsupported bug type: {bug_type}")

        bug_type_code = self.bug_conversion_table[bug_type]

        if definitions.KEY_SOURCE not in bug_info:
            error_exit(
                f"Missing memory source information in benchmark, required for {self.name}"
            )
        if definitions.KEY_SINK not in bug_info:
            error_exit(
                f"Missing memory sink information in benchmark, required for {self.name}"
            )

        saver_source_info = dict()
        bench_source_info = bug_info[definitions.KEY_SOURCE]
        if bench_source_info["src-file"]:
            saver_source_info["filename"] = bench_source_info["src-file"]
        saver_source_info["procedure"] = bench_source_info["procedure"]
        saver_source_info["line"] = bench_source_info["line"]
        config_info["source"] = {"node": saver_source_info, "exp": None}

        saver_sink_info = dict()
        bench_sink_info = bug_info[definitions.KEY_SINK]
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
        emitter.normal("\t\t\t preparing subject for repair with " + self.name)
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)
        config_path = join(self.dir_expr, self.name, "bug.json")
        self.populate_config_file(bug_info, config_path)
        time = datetime.now()
        bug_type = bug_info[definitions.KEY_BUG_TYPE]
        if bug_type == "Memory Leak":
            compile_command = (
                "infer -j 20 -g --headers --check-nullable-only -- make -j20"
            )
        else:
            compile_command = (
                "infer -j 20 run -g --headers --check-nullable-only -- make -j20"
            )
        emitter.normal("\t\t\t\t compiling subject with " + self.name)
        self.run_command(compile_command, dir_path=dir_src)
        emitter.normal(
            "\t\t\t\t compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        time = datetime.now()
        emitter.normal("\t\t\t\t analysing subject with " + self.name)
        analysis_command = "infer saver --pre-analysis-only "
        self.run_command(analysis_command, dir_path=dir_src)
        emitter.normal(
            "\t\t\t\t analysis took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

        return config_path

    def run_repair(self, bug_info, config_info):
        config_path = self.prepare(bug_info)
        super(SAVER, self).run_repair(bug_info, config_info)
        if values.only_instrument:
            return
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )

        if values.use_container:
            emitter.error(
                "[Exception] unimplemented functionality: SAVER docker support not implemented"
            )
            error_exit("Unhandled Exception")

        self.timestamp_log_start()
        saver_command = "cd {};".format(join(self.dir_expr, "src"))
        saver_command += "timeout -k 5m {0}h saver --error-report {1} ".format(
            str(timeout_h), config_path
        )
        bug_type = bug_info[definitions.KEY_BUG_TYPE]
        if bug_type in ["Double Free", "Use After Free"]:
            saver_command += " --analysis-with-fimem "
        saver_command += "{0} >> {1} 2>&1 ".format(
            additional_tool_param, self.log_output_path
        )
        status = execute_command(saver_command)

        self.process_status(status)

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        copy_command = "cp -rf {}/saver {}".format(self.dir_expr, self.dir_output)
        self.run_command(copy_command)
        # infer_output = join(self.dir_expr, "src", "infer-out")
        # copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        # self.run_command(copy_command)
        super(SAVER, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t[warning] no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
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
            emitter.error("\t\t\t\t[error] error detected in logs")

        return self._space, self._time, self._error
