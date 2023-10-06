import os
from os.path import join
from app.core import container
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Brafar(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "linnaxie/brafar-python"
        self.hash_digest = "sha256:190cb9cea70bca70c4c7354a9463e03067188af8fe4ce92843a0e713d1afaeb7"

    def run_repair(self, bug_info, repair_config_info):
        super(Brafar, self).run_repair(bug_info, repair_config_info)
        self.timestamp_log_start()
        status = self.run_command(
            "timeout -k 5m {}h python3 run.py -d {} -q src -s 100 -o {} {}".format(
                repair_config_info[self.key_timeout],
                self.dir_expr,
                "/output/patches",
                repair_config_info[self.key_tool_params],
            ),
            self.log_output_path,
            dir_path="/home/linna/brafar-python",
        )
        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        # self.run_command("mkdir /output")
        # self.run_command("mkdir /output/patches")
        # self.run_command("bash -c 'cp {}/src/*.diff /output/patches'".format(self.dir_expr))
        super(Brafar, self).save_artifacts(dir_info)

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

        # extract information from output log
        return self.stats
