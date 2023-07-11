import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Refactory(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/refactory"

    def run_repair(self, bug_info, repair_config_info):
        super(Refactory, self).run_repair(bug_info, repair_config_info)

        self.timestamp_log_start()
        status = self.run_command(
            "timeout -k 5m {}h /home/huyang/conda/bin/python3 run.py -d {} -q src -s 100 {}".format(
                repair_config_info[self.key_timeout],
                self.dir_expr,
                repair_config_info[self.key_tool_params] or "-o -m -b",
            ),
            self.log_output_path,
            dir_path="/home/huyang/refactory",
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
        self.run_command("mkdir /output")
        self.run_command("bash -c 'cp {}/src/*.csv /output/'".format(self.dir_expr))
        super(Refactory, self).save_artifacts(dir_info)

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
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")

            for line in log_lines:
                if line.startswith("fail"):
                    self.stats.error_stats.is_error = True

        return self.stats
