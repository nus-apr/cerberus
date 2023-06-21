import os
import re
from datetime import datetime
from os.path import join

from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class Hippodrome(AbstractAnalyzeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/hippodrome:latest"

    def run_analysis(self, bug_info, repair_config_info):
        super(Hippodrome, self).run_analysis(bug_info, repair_config_info)

        timeout_h = str(repair_config_info[self.key_timeout])

        # start running
        self.timestamp_log()

        run_dir = self.dir_expr
        hippodrome_command = "timeout -k 5m {}h java -jar /hippodrome/target/hippodrome-1.0-jar-with-dependencies.jar -c CONFIG.json".format(
            timeout_h
        )
        if self.is_dir(join(self.dir_expr, "src")):
            hippodrome_command = "timeout -k 5m {}h java -jar /hippodrome/target/hippodrome-1.0-jar-with-dependencies.jar -c ../CONFIG.json".format(
                timeout_h
            )
            run_dir = join(self.dir_expr, "src")

        status = self.run_command(hippodrome_command, self.log_output_path, run_dir)

        self.process_status(status)

        self.timestamp_log()
        self.emit_highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        self.run_command("mkdir -p /output/", "/dev/null", "/")
        self.run_command("cp -rf {} /output/".format(self.dir_expr))
        super().save_artefacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(repair_conf_id, self.name.lower(), bug_id),
        )
        is_error = False
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "ERROR:" in line:
                is_error = True
                self.stats.error_stats.is_error = True
            if "Patch ID:" in line:
                count = int(line.split(":")[-1])
                self.stats.patches_stats.generated = (
                    self.stats.patches_stats.enumerations
                ) = max(self.stats.patches_stats, count)
            if "Applying Patch ID" in line:
                self.stats.patches_stats.plausible += 1
        if is_error:
            self.emit_error("error detected in logs")

        return self.stats
