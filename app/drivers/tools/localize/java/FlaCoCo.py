import os
import re
from os.path import join

from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class FlaCoCo(AbstractLocalizeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/flacoco:latest"
        self.id = ""

    def run_localization(self, bug_info, localization_config_info):
        super(FlaCoCo, self).run_localization(bug_info, localization_config_info)
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(localization_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = localization_config_info[self.key_tool_params]

        formula = bug_info.get("fl_formula", "Ochiai").upper()

        env = {}
        self.timestamp_log_start()
        localize_command = "timeout -k 5m {}h java -jar /flacoco/target/flacoco-1.0.7-SNAPSHOT-jar-with-dependencies.jar -f {} --projectpath {} {} -o {}".format(
            timeout,
            formula,
            join(self.dir_expr, "src"),
            additional_tool_param,
            join(self.dir_output, "localilzation.csv"),
        )

        status = self.run_command(localize_command, self.log_output_path, env=env)
        self.process_status(status)

        if self.is_file(join(self.dir_output, "localilzation.csv")):
            localization = []
            lines = self.read_file(join(self.dir_output, "localization.csv"))
            for entry in lines:
                path, line, score = entry.split(",")
                localization.append(
                    {
                        "source_file": path,
                        "line_numbers": [line],
                        "score": score,
                    }
                )
            new_metadata = {
                "generator": "flacoco",
                "confidence": "1",
                "localization": localization,
            }
            self.write_json([new_metadata], join(self.dir_output, "meta-data.json"))

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        output_file = join(self.dir_output, "localilzation.csv")
        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False
        if self.is_file(output_file):
            output_lines = self.read_file(output_file, encoding="iso-8859-1")
            self.stats.fix_loc_stats.plausible = len(output_lines)
            self.stats.fix_loc_stats.generated = len(output_lines)

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
