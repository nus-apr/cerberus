import os
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class RepairLlama(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(RepairLlama, self).__init__(self.name)
        self.image_name = "andre15silva/repairllama:latest"
        self.hash_digest = (
            "sha256:84e6a0edc81b9edd08158c41a0ada00aa96ee9dbda699435c61f7f07669af513"
        )

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """
        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])
        patch_directory = join(self.dir_output, "patches")

        # execute repair tool
        command = (
            f"python3.10 main.py "
            f"--dir_java_src {dir_java_src} "
            f"--dir_test_src {dir_test_src} "
            f"--dir_java_bin {dir_java_bin} "
            f"--dir_test_bin {dir_test_bin} "
            f"--patch_directory {patch_directory}"
        )

        timeout_h = str(task_config_info[self.key_timeout])
        repair_command = f"timeout -k 5m {timeout_h}h {command} "
        self.timestamp_log_start()
        status = self.run_command(repair_command, log_file_path=self.log_output_path)
        self.process_status(status)
        self.timestamp_log_end()
