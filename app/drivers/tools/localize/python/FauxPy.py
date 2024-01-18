import os
import re
from os.path import join

from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class FauxPy(AbstractLocalizeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/fauxpy:latest"
        self.id = ""

    def run_localization(self, bug_info, localization_config_info):
        super(FauxPy, self).run_localization(bug_info, localization_config_info)
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(localization_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        additional_tool_param = localization_config_info[self.key_tool_params]

        self.timestamp_log_start()
        localize_command = 'bash -c \'timeout -k 5m {}h python3 -m pytest --src . --family sbfl {} --exclude "[$(ls | grep test | grep .py | tr "\\n" "," | sed "s/,$//")]"\''.format(
            timeout,
            additional_tool_param,
        )

        formula = bug_info.get("fl_formula", "Ochiai")

        status = self.run_command(
            localize_command, self.log_output_path, dir_path=join(self.dir_expr, "src")
        )

        if status == 1:
            # The test suite has failing tests but this is generally what we want to so we change the code to success if the report is generated
            report_list = self.list_dir(join(self.dir_expr), regex="FauxPyReport*")
            if len(report_list) > 0:
                self.run_command(
                    "bash -c 'cp -r {} {}'".format(report_list[0], self.dir_output),
                    dir_path=self.dir_expr,
                )
                self.run_command(
                    "bash -c 'cp {}/Scores_{}.csv {}'  ".format(
                        report_list[0],
                        formula,
                        join(self.dir_output, "localization.csv"),
                    ),
                    dir_path=self.dir_expr,
                )
                status = 0

        self.process_status(status)

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
                if "statistics" in line:
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
