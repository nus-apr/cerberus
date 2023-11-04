import csv
import os
import time
from os.path import join

from app.core import definitions, values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class RewardRepairI(AbstractRepairTool):
    """
    Requirements for this tool: 2GB of VRAM (for GPUs)
    """

    SECS_PER_HOUR = 3600

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "thanhlecong/rewardrepair:cerberus"
        self.bug_name = ""
        self.dir_fl = join(values.dir_main, "localization", "ochiai")

    def run_repair(self, bug_info, repair_config_info):
        super(RewardRepairI, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        top_n = 200

        tool_dir = "/repair/RewardRepair"

        if repair_config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
            if len(bug_info[self.key_fix_lines]) == 0:
                self.error_exit("no line number to fix")

            locations = [
                (
                    bug_info[self.key_fix_file].replace(".", "/"),
                    bug_info[self.key_fix_lines][0],
                )
            ]
        else:
            fl_file = join(self.dir_fl, f"{bug_info[self.key_bug_id]}.csv")
            if not os.path.isfile(fl_file):
                self.error_exit(f"Localization file not found: {fl_file}")

            with open(fl_file, newline="") as f:
                reader = csv.reader(f)
                locations = [
                    (the_class.replace(".", "/"), line)
                    for (the_class, line, _) in reader
                ]

        self.timestamp_log_start()
        time_start = time.time()

        timeout_h = float(repair_config_info[self.key_timeout])

        for fix_file, fix_line in locations:
            out_dir = join(self.dir_output, f"{fix_file.replace('/', '.')}-{fix_line}")
            self.run_command(f"mkdir -p {out_dir}", self.log_output_path, tool_dir)

            self.bug_name = bug_info[self.key_bug_id]
            file = join(bug_info[self.key_dir_source], f"{fix_file}.java")

            elapsed_h = (time.time() - time_start) / self.SECS_PER_HOUR
            if elapsed_h > timeout_h:
                break

            repair_command = (
                f"""bash -c 'export PATH=$PATH:/root/defects4j/framework/bin &&"""
                f""" timeout -k 5m {timeout_h - elapsed_h}h python3 main.py --task repair"""
                f""" --bug_id {self.bug_name.replace("-", "_")}"""
                f""" --src_dir {join(self.dir_expr, "src")}"""
                f""" --buggy_file {join(file)} --buggy_loc {fix_line}"""
                f""" --top_n_patches {top_n}"""
                f""" --output_folder {out_dir}'"""
            )
            status = self.run_command(repair_command, self.log_output_path, tool_dir)
            self.process_status(status)

            elapsed_h = (time.time() - time_start) / self.SECS_PER_HOUR
            if elapsed_h > timeout_h:
                break

            validation_command = (
                f"""bash -c 'export PATH=$PATH:/root/defects4j/framework/bin &&"""
                f""" timeout -k 5m {timeout_h - elapsed_h}h python3 main.py --task validate"""
                f""" --bug_id {self.bug_name.replace("-", "_")}"""
                f""" --src_dir {join(self.dir_expr, "src")}"""
                f""" --buggy_file {join(file)} --buggy_loc {fix_line}"""
                f""" --output_folder {out_dir}'"""
            )

            status = self.run_command(
                validation_command, self.log_output_path, tool_dir
            )
            self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = (
                log_lines[0].replace("\n", "").replace("Start Time: ", "")
            )
            self.stats.time_stats.timestamp_end = (
                log_lines[-1].replace("\n", "").replace("End Time: ", "")
            )

            if not self.stats.error_stats.is_error:
                # TODO: Implement later
                self.stats.patch_stats.generated = 500
                self.stats.patch_stats.enumerations = 500
                self.stats.patch_stats.plausible = 1
                self.stats.patch_stats.non_compilable = 0

        return self.stats
