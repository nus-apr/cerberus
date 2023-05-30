import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Recoder(AbstractRepairTool):
    """
    Requirements for this tool:
    15 GB of VRAM, at most 7.0 CUDA (e.g. Nvidia V100) compute and 20 GB of RAM
    """

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "zqh111/recoder:interface"
        self.bug_name = ""

    def run_repair(self, bug_info, repair_config_info):
        super(Recoder, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(repair_config_info[self.key_timeout])

        if not self.use_gpu:
            self.error_exit("cannot run Recorder without a GPU")

        self.bug_name = bug_info[self.key_bug_id]
        # generate patches
        self.timestamp_log_start()
        recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 testDefect4jv21.py {}'".format(  # currently supporting only defects4j
            timeout_h,
            bug_info[self.key_bug_id],
        )
        status = self.run_command(
            recorder_command, self.log_output_path, "/root/Repair/"
        )

        recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 repair.py {}'".format(
            timeout_h,
            bug_info[self.key_bug_id],
        )

        status = self.run_command(
            recorder_command,
            self.log_output_path,
            "/root/Repair/",
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
        self.emit_normal("reading output")

        # count number of patch files
        self.stats.patches_stats.generated = 1

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")

        if not self.stats.error_stats.is_error:
            self.run_command(
                "cp /root/Repair/patches/{}patch.txt /output/".format(self.bug_name)
            )
            self.stats.patches_stats.generated = 1
            self.stats.patches_stats.enumerations = 1
            self.stats.patches_stats.plausible = 1
            self.stats.patches_stats.non_compilable = 0

        return self.stats
