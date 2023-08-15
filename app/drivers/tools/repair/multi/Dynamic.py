import os

from app.core import values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Dynamic(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bindings = {
            values.dir_dynamic: {
                "bind": "/tool",
                "mode": "rw",
            }
        }
        super().__init__(self.name)
        # preferably change to a container with the dependencies to reduce setup time
        self.image_name = "ubuntu:22.04"

    def run_repair(self, bug_info, repair_config_info):
        super(Dynamic, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(repair_config_info[self.key_timeout])
        timeout_m = str(float(timeout_h) * 60)

        # generate patches
        self.timestamp_log_start()
        repair_command = "echo 0"

        self.run_command("bash /tool/setup.sh", self.log_output_path)

        status = self.run_command(repair_command, self.log_output_path)

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
        super(Dynamic, self).save_artifacts(dir_info)

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

        return self.stats
