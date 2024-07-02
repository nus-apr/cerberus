import json
import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class JoernSBFL(AbstractLocalizeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "wolffdy/joern-sbfl-crash-analysis:latest"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]

        if self.key_bin_path not in bug_info:
            self.emit_error("No binary path found")

        self.run_command(
            f"""bash -c '{os.path.join(self.dir_setup, bug_info[self.key_clean_script])}'""",
        )

        self.run_command(
            f"""bash -c '{os.path.join(self.dir_setup, bug_info[self.key_config_script])}'""",
        )
        self.run_command(
            f"""bash -c '{os.path.join(self.dir_setup, bug_info[self.key_build_script])}'""",
        )
        # For using with network disabled, <<does not work>> but will work if this
        #   command is run manually in the container
        # self.run_command(
        #     f"""echo 'nameserver 8.8.8.8' > /etc/resolv.conf""",
        # )

        self.timestamp_log_start()

        self.emit_normal(f"Running {self.name}")

        metadata_loc = os.path.join(self.dir_expr, "meta-data.json")
        bug_info["src"] = {"root_abspath": os.path.join(self.dir_expr, "src")}
        bug_info["test_dir_abspath"] = self.dir_setup
        self.write_json(bug_info, metadata_loc)

        self.run_command(
            "python3 /opt/crash_analysis.py {}".format(metadata_loc),
            log_file_path=self.log_output_path,
            dir_path="/opt/",
        )

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        self.emit_normal("reading output")
        output_files = self.list_dir(self.dir_output, "meta-data.json")
        output_json = None
        if output_files:
            output_json = output_files[0]

        if not output_json:
            self.emit_warning("no output json file found")
            return self.stats

        output_info = self.read_json(output_json)
        if not isinstance(output_info, Dict):
            self.emit_error("expected analysis to provide a json object")
            return self.stats
        analysis_info = output_info[self.key_analysis_output]
        localization_list = analysis_info[0][self.key_localization]
        if localization_list:
            fix_files = set()
            fix_lines = list()
            for _l in localization_list:
                fix_files.add(_l.get(self.key_fix_file))
                fix_lines += _l.get(self.key_fix_lines, [])
            self.stats.fix_loc_stats.fix_locs = len(fix_lines)
            self.stats.fix_loc_stats.source_files = len(fix_files)

        return self.stats
