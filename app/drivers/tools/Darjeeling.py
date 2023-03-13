import multiprocessing as mp
import os
import re
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class Darjeeling(AbstractTool):
    """ """

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Darjeeling, self).__init__(self.name)
        self.image_name = "rshariffdeen/darjeeling"

    def instrument(self, bug_info):
        """
        Instrumentation for the experiment as needed by the tool
        - requires sudo
        """
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.current_profile_id)
        buggy_file = bug_info[definitions.KEY_FIX_FILE]
        self.log_instrument_path = (
            self.dir_logs
            + "/"
            + conf_id
            + "-"
            + self.name
            + "-"
            + bug_id
            + "-instrument.log"
        )
        command_str = "sudo bash instrument.sh {} {}".format(
            self.dir_base_expr, buggy_file
        )
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of "
                + self.name
                + "; exit code "
                + str(status)
            )
        return

    def repair(self, bug_info, config_info):
        super(Darjeeling, self).repair(bug_info, config_info)
        if values.only_instrument:
            return
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        emitter.normal("\t\t\t running repair with " + self.name)
        timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(
                str(values.current_profile_id), self.name.lower(), bug_id
            ),
        )
        dir_patch = self.dir_output + "/patches"

        mkdir_command = "sudo mkdir -p {}".format(dir_patch)
        self.run_command(mkdir_command, self.log_output_path, self.dir_expr)

        repair_command = "timeout -k 5m {}h  ".format(str(timeout))
        if self.container_id:
            repair_command += "sudo "
        repair_command += "darjeeling repair --continue --patch-dir {} ".format(
            dir_patch
        )
        repair_command += " --threads {} ".format(mp.cpu_count())
        repair_command += additional_tool_param + " "
        if values.dump_patches:
            repair_command += " --dump-all "
        repair_command += " repair.yml"
        self.timestamp_log_start()
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_expr + "/src"
        )
        self.timestamp_log_end()
        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id)
        self.log_analysis_path = join(
            self.dir_logs,
            "{}-{}-{}-analysis.log".format(conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        time_stamp_first_plausible = None
        time_stamp_first_validation = None
        time_stamp_first_compilation = None

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "evaluated candidate" in line:
                    self._space.enumerations += 1
                    if time_stamp_first_validation is None:
                        time_stamp_first_validation = line.split(" | ")[0]
                elif "found plausible patch" in line:
                    self._space.plausible += 1
                    if time_stamp_first_plausible is None:
                        time_stamp_first_plausible = line.split(" | ")[0]
                elif "validation time: " in line:
                    time = (
                        line.split("validation time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self._time.total_validation += float(time)
                elif "build time: " in line:
                    time = (
                        line.split("build time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self._time.total_build += float(time)
                    if time_stamp_first_compilation is None:
                        time_stamp_first_compilation = line.split(" | ")[0]
                elif "possible edits" in line:
                    self._space.size = int(line.split(": ")[2].split(" ")[0])
                elif "plausible patches" in line:
                    self._space.plausible = int(
                        line.split("found ")[-1]
                        .replace(" plausible patches", "")
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )

        self._space.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if values.use_valkyrie else "patches",
                )
            )
        )

        return self._space, self._time, self._error
