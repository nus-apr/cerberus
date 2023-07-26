import multiprocessing as mp
import os
import re
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Darjeeling(AbstractRepairTool):
    """ """

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/darjeeling"

    def instrument(self, bug_info):
        """
        Instrumentation for the experiment as needed by the tool
        - requires sudo
        """
        self.emit_normal(" instrumenting for " + self.name)
        bug_id = bug_info[self.key_bug_id]
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        buggy_file = bug_info[self.key_fix_file]
        self.log_instrument_path = (
            self.dir_logs
            + "/"
            + task_conf_id
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
            self.error_exit(
                "error with instrumentation of "
                + self.name
                + "; exit code "
                + str(status)
            )
        return

    def run_repair(self, bug_info, repair_config_info):
        super(Darjeeling, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(
                str(self.current_task_profile_id.get("NA")), self.name.lower(), bug_id
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
        if self.is_dump_patches:
            repair_command += " --dump-all "
        repair_command += " repair.yml"
        self.timestamp_log_start()
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_expr + "/src"
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
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
            self.emit_warning("[warning] no log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        time_stamp_first_plausible = None
        time_stamp_first_validation = None
        time_stamp_first_compilation = None

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "evaluated candidate" in line:
                    self.stats.patch_stats.enumerations += 1
                    if time_stamp_first_validation is None:
                        time_stamp_first_validation = line.split(" | ")[0]
                elif "found plausible patch" in line:
                    self.stats.patch_stats.plausible += 1
                    if time_stamp_first_plausible is None:
                        time_stamp_first_plausible = line.split(" | ")[0]
                elif "validation time: " in line:
                    time = (
                        line.split("validation time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self.stats.time_stats.total_validation += float(time)
                elif "build time: " in line:
                    time = (
                        line.split("build time: ")[-1]
                        .strip()
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )
                    self.stats.time_stats.total_build += float(time)
                    if time_stamp_first_compilation is None:
                        time_stamp_first_compilation = line.split(" | ")[0]
                elif "possible edits" in line:
                    self.stats.patch_stats.size = int(line.split(": ")[2].split(" ")[0])
                elif "plausible patches" in line:
                    self.stats.patch_stats.plausible = int(
                        line.split("found ")[-1]
                        .replace(" plausible patches", "")
                        .split("\x1b")[0]
                        .split(".0")[0]
                    )

        self.stats.patch_stats.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if self.use_valkyrie else "patches",
                )
            )
        )

        return self.stats
