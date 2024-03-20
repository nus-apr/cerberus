import base64
import json
import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


CUR_DIR = os.path.abspath(__file__)[: os.path.abspath(__file__).rindex("/") + 1]


class AIxCCRepairSFT(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "jiang719/aixcc-repair-sft:latest"
        self.bug_name = ""
        self.hash_digest = ""

    def run_repair(self, bug_info, repair_config_info):
        super(AIxCCRepairSFT, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        self.bug_name = bug_info[self.key_bug_id]

        tool_info = {
            "dir_logs": self.dir_logs,
            "dir_setup": self.dir_setup,
            "dir_expr": self.dir_expr,
            "dir_output": self.dir_output
        }
        bug_info_encoded = base64.b64encode(json.dumps(bug_info).encode()).decode()
        tool_info_encoded = base64.b64encode(json.dumps(tool_info).encode()).decode()
        
        timeout_h = str(repair_config_info[self.key_timeout])
        repair_command = f"bash -c 'cd /home/aixcc-repair/api && python sft_repair.py {bug_info_encoded} {tool_info_encoded}'"
        repair_command = f"timeout -k 5m {timeout_h}h {repair_command} "
        self.timestamp_log_start()
        status = self.run_command(
            repair_command,
            self.log_output_path,
            dir_path="/home/aixcc-repair/",
        )

        self.run_command(f"cp /home/result.json {self.dir_output}/result.json")

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
