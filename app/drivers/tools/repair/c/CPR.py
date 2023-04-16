import os
import re
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class CPR(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/cpr"
        self.id = ""

    def run_repair(self, bug_info, config_info):
        super(CPR, self).run_repair(bug_info, config_info)
        if self.is_instrument_only:
            return
        conf_id = str(self.current_profile_id.get("NA"))
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.id = bug_id
        timeout = str(config_info[self.key_test_timeout])
        dir_patch = join(self.dir_output, "patches")
        mkdir_command = "mkdir -p " + dir_patch
        self.run_command(mkdir_command, self.log_output_path, "/")
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        conf_path = join(self.dir_expr, "cpr", "repair.conf")
        timeout_m = str(float(timeout) * 60)
        test_id_list = ",".join(bug_info[definitions.KEY_FAILING_TEST])
        seed_id_list = ",".join(bug_info[definitions.KEY_PASSING_TEST])

        additional_tool_param = config_info[self.key_tool_param]
        self.timestamp_log_start()
        cpr_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h cpr --conf=".format(
                timeout
            )
            + conf_path
            + " "
        )
        cpr_command += " --seed-id-list=" + seed_id_list + " "
        cpr_command += " --test-id-list=" + test_id_list + " "
        cpr_command += "{0} --time-duration={1}' >> {2} 2>&1 ".format(
            additional_tool_param, str(timeout_m), self.log_output_path
        )
        status = self.run_command(cpr_command, self.log_output_path)

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        self.emit_normal(" saving artifacts of " + self.name)
        dir_patch = join(self.dir_output, "patches")
        self.run_command("cp -rf /CPR/output/{} {}".format(self.id, dir_patch))
        super(CPR, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        conf_id = str(self.current_profile_id.get("NA"))
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
            self.emit_warning("no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "|P|=" in line:
                    self._space.plausible = int(
                        line.split("|P|=")[-1]
                        .strip()
                        .replace("^[[0m", "")
                        .split(":")[0]
                    )
                elif "number of concrete patches explored" in line:
                    count_enumerations = int(
                        line.split("number of concrete patches explored: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self._space.enumerations = count_enumerations
                elif "Runtime Error" in line:
                    self._error.is_error = True
                elif "statistics" in line:
                    is_timeout = False

        if self._error.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self._space, self._time, self._error
