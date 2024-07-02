import json
import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.multi.Prompter import Prompter


class IterativePrompter(Prompter):
    def __init__(self) -> None:
        super(IterativePrompter, self).__init__()
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_user = "ubuntu"
        self.runs_as_root = False
        self.image_name = "rshariffdeen/prompter"
        self.sudo_password = "ubuntu"
        self.config_file: str = ""
        self.output_path: str = ""

    def generate_config_file(self, bug_info: Dict[str, Any]) -> str:
        repair_config_path = os.path.join(self.dir_expr, "src", "repair.json")
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
        config_object: Dict[str, Any] = dict()
        config_object["language"] = bug_info[self.key_language].lower()
        config_object["output_dir"] = self.output_path
        config_object["cwe_id"] = bug_info["cwe_id"]

        fix_locations = []
        localization_list = bug_info[self.key_localization]
        for result in localization_list:
            source_file = result[self.key_fix_file]
            if self.dir_expr not in source_file:
                source_file = join(self.dir_expr, "src", source_file)
            line_numbers = result[self.key_fix_lines]
            for _l in line_numbers:
                fix_locations.append({"source_path": source_file, "line_number": _l})
        config_object["localization"] = fix_locations
        patch_list = bug_info["patches"]
        updated_patch_list = []
        validation_info = bug_info["validation_output"][0]["validation_result"]
        validation_result = {}
        for _id, _result in validation_info:
            _, patch_id = _id.split(":")
            validation_result[patch_id] = _result
        for _p in patch_list:
            _p_id = _p["patch_file"]
            _result_id = validation_result[patch_id]
            result_type_mapping = {
                "fixed failing": "failure-fixing",
                "invalid patch": "invalid",
                "cannot build": "invalid",
                "incorrect patch": "incorrect",
            }
            _result = result_type_mapping[_result_id]
            if _p_id in validation_result:
                _p["patch_type"] = _result
                updated_patch_list.append(_p)
        config_object["patches"] = updated_patch_list
        self.write_file([json.dumps(config_object)], repair_config_path)
        return repair_config_path

    def create_meta_data(self) -> None:
        patch_list = []
        patch_info_json = join(self.dir_output, "generated_feedback_patches.json")
        if self.is_file(patch_info_json):
            patch_info = self.read_json(patch_info_json)
            if isinstance(patch_info, Dict):
                patch_list = patch_info["patches"]
        metadata = {
            "patches_dir": join(self.dir_output, "patches"),
            "patches": patch_list,
        }
        self.write_json(
            metadata,
            join(self.dir_output, "meta-data.json"),
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

        repair_command = (
            f"timeout -k 5m {timeout}h python feedback.py {self.config_file}"
        )
        self.emit_debug(repair_command)
        status = self.run_command(
            repair_command, self.log_output_path, "/home/ubuntu/prompter"
        )

        copy_cmd = f"cp -rf {self.output_path}/* {self.dir_output}"
        self.run_command(copy_cmd, run_as_sudo=True)
        self.process_status(status)
        self.create_meta_data()
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()
