import os
import re
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
        self.image_name = "rshariffdeen/prompter"
        self.sudo_password = "ubuntu"

    def locate(self) -> None:
        pass

    def create_config(self) -> None:
        config_file_path = "/home/ubuntu/prompter/config.toml"
        google_auth_json_path = "/home/ubuntu/prompter/google-key.json"
        google_auth_data = {
            "type": "service_account",
            "universe_domain": "googleapis.com",
            "auth_uri": "https://accounts.google.com/o/oauth2/auth",
            "token_uri": "https://oauth2.googleapis.com/token",
            "auth_provider_x509_cert_url": "https://www.googleapis.com/oauth2/v1/certs",
        }
        google_auth_secret_data = self.api_keys.get(self.key_gemini_token, dict())
        for key, value in google_auth_secret_data.items():
            google_auth_data[key] = value
        openai_token = self.api_keys.get(self.key_openai_token, None)
        anthropic_token = self.api_keys.get(self.key_anthropic_token, None)
        huggingface_token = self.api_keys.get(self.key_huggingface_token, "TOKEN")

        if not openai_token and not anthropic_token:
            self.error_exit(
                f"{self.name} requires at least one API key for OpenAI or Anthropic"
            )
        self.write_json(google_auth_data, google_auth_json_path)
        self.write_file(
            [
                "[huggingface]\n",
                f'hf_token = "{huggingface_token}"\n',
                "[anthropic]\n",
                f'anthropic_token = "{anthropic_token}"\n',
                "[openai]\n",
                f'openai_token = "{openai_token}"\n',
                "[google]\n",
                f'gemini_token = "google-key.json"\n',
                "[data]\n",
                'data_path = "./megavul_simple.json"\n',
                'chroma_path = "./data_store"\n',
                'collection_name = "megavul"\n',
                "\n",
            ],
            config_file_path,
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

        self.timestamp_log_start()
        timeout = str(task_config_info[self.key_timeout])

        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        self.output_path = join(
            "/home",
            "ubuntu",
            "prompter",
            "output",
            bug_info[self.key_benchmark],
            bug_info[self.key_subject],
            bug_info[self.key_bug_id],
        )
        self.run_command(f"mkdir -p {self.output_path}")
        self.create_config()
        file_path = join(
            self.dir_expr, "src", bug_info[self.key_localization][0][self.key_fix_file]
        )

        self.emit_debug(bug_info)
        fix_line = bug_info[self.key_localization][0][self.key_fix_lines][0]
        cwe_id = bug_info["cwe_id"]
        repair_command = f"timeout -k 5m {timeout}h python3 cli.py {file_path} {cwe_id}  {fix_line} {self.output_path}"
        self.emit_debug(repair_command)
        status = self.run_command(
            repair_command, self.log_output_path, "/home/ubuntu/prompter"
        )

        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        copy_cmd = f"cp -rf {self.output_path}/* {self.dir_output}"
        self.run_command(copy_cmd, run_as_sudo=True)
        super(Prompter, self).save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight("log File: " + self.log_output_path)

        if self.stats.error_stats.is_error:
            self.emit_error("error detected in logs")

        self.stats.patch_stats.plausible = 0
        self.stats.patch_stats.non_compilable = 0
        self.stats.patch_stats.size = 0
        self.stats.patch_stats.enumerations = 0

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")

            for line in log_lines:
                if "Received response" in line:
                    self.stats.patch_stats.enumerations += 1

        self.stats.patch_stats.size = self.stats.patch_stats.enumerations
        # count number of patch files
        self.dir_patch = join(self.output_path, "patches")
        list_output_dir = self.list_dir(self.dir_patch)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".diff" in name]
        )

        return self.stats
