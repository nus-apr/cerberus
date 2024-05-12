import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Prompter(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Prompter, self).__init__(self.name)
        self.image_user = "ubuntu"
        self.runs_as_root = False
        self.image_name = "prompter"
        self.sudo_password = "ubuntu"

    def locate(self) -> None:
        pass

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        self.timestamp_log_start()
        timeout = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        self.run_command(
            "bash -c \"echo 'ubuntu\\n' | sudo -S mkdir -p -m 777 {}\"".format(
                self.dir_output
            )
        )

        self.append_file(
            [
                "[anthropic]\n",
                'anthropic_token = "INSERT ANTHROPIC KEY HERE"\n',
                "[openai]\n" 'openai_token = "INSERT OPENAI DRIVER HERE"\n',
                "\n",
            ],
            "/home/ubuntu/prompter/config.toml",
        )

        file_path = join(
            self.dir_expr, "src", bug_info[self.key_localization][0][self.key_fix_file]
        )

        self.emit_debug(bug_info)

        repair_command = f"timeout -k 5m {timeout}h python3 main.py {file_path} {bug_info['cwe_id']} {self.dir_output} {bug_info[self.key_localization][0][self.key_fix_lines][0]}"
        self.emit_debug(repair_command)
        status = self.run_command(
            repair_command, self.log_output_path, "/home/ubuntu/prompter"
        )

        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        # dir_results = join(self.dir_expr, "result")
        # task_conf_id = str(self.current_task_profile_id.get("NA"))
        # self.log_stats_path = join(
        #     self.dir_logs,
        #     "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        # )

        # if not self.log_output_path or not self.is_file(self.log_output_path):
        #     self.emit_warning("[warning] no log file found")
        #     return self.stats

        # self.emit_highlight(f"output log file: {self.log_output_path}")

        # self.stats.patch_stats.generated = len(
        #     self.list_dir(join(self.dir_output, "patches"))
        # )

        return self.stats
