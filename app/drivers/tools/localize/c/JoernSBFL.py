import os
import re
from typing import Any
from typing import Dict
from typing import List
from os.path import join
import json

from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class JoernSBFL(AbstractLocalizeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "joern-sbfl-crash-analysis:latest"
        self.id = ""

    def run_localization(self, bug_info : Dict[str, Any], localization_config_info  : Dict[str, Any]):
        super(JoernSBFL, self).run_localization(bug_info, localization_config_info)
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

        if self.key_bin_path not in bug_info:
            self.emit_error("No binary path found")

        self.run_command(
            f"""bash -c '{os.path.join(self.dir_setup, bug_info["config_script"])}'""",
        )
        self.run_command(
            f"""bash -c '{os.path.join(self.dir_setup, bug_info["build_script"])}'""",
        )
        self.run_command(
            f"""echo 'nameserver 8.8.8.8' > /etc/resolv.conf""",
        )

        self.timestamp_log_start()

        self.emit_normal("Running tool...")

        bug_info["src"] = {"root_abspath": os.path.join(self.dir_expr, "src")}
        bug_info["output_dir_abspath"] = self.dir_output
        bug_info["test_dir_abspath"] = self.dir_setup
        self.write_json(bug_info, os.path.join(self.dir_expr, "meta-data.json"))

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        return self.stats
