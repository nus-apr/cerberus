import os
import re
from datetime import datetime
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.core.utilities import execute_command
from app.drivers.tools.analyze.AbstractAnalysisTool import AbstractAnalysisTool


class Infer(AbstractAnalysisTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK",
        "Use After Free": "USE_AFTER_FREE",
        "Double Free": "DOUBLE_FREE",
    }

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Infer, self).__init__(self.name)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        emitter.normal("\t\t\t preparing subject for analysis with " + self.name)
        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        time = datetime.now()
        compile_command = (
            "infer -j 20 -g compile -- make -j20"
        )

        emitter.normal("\t\t\t\t compiling subject with " + self.name)
        self.run_command(compile_command, dir_path=dir_src)
        emitter.normal(
            "\t\t\t\t compilation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )



    def run_analysis(self, bug_info, config_info):
        self.prepare(bug_info)
        super(Infer, self).run_analysis(bug_info, config_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]

        self.timestamp_log_start()
        dir_src = join(self.dir_expr, "src")
        saver_command = "timeout -k 5m {0}h infer analyze {1} -- make -j20 ".format(
            str(timeout_h), additional_tool_param
        )

        status = self.run_command(saver_command, dir_path=dir_src,
                                  log_file_path=self.log_output_path)
        if status != 0:
            emitter.warning(
                "\t\t\t[warning] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        infer_output = join(self.dir_expr, "src", "infer-out")
        copy_command = "cp -rf {} {}".format(infer_output, self.dir_output)
        self.run_command(copy_command)
        super(Infer, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(conf_id, self.name.lower(), bug_id),
        )
        is_error = False
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "ERROR:" in line:
                self._error.is_error = True
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")

        return self._space, self._time, self._error
