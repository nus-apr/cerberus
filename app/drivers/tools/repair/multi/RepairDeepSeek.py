import base64
import json
import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractLLMRepairTool import AbstractLLMRepairTool


CUR_DIR = os.path.abspath(__file__)[: os.path.abspath(__file__).rindex("/") + 1]


class RepairDeepSeek(AbstractLLMRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.bug_name = ""
        self.image_name = "jiang719/aixcc-repair-sft-deepseek"
        self.hash_digest = (
            "sha256:b72ef1c2c3a06d50431fa9731d8e1c171de54f2da3b525a04dc58a718d77b4ce"
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
        self.bug_name = bug_info[self.key_bug_id]
        tool_info = {
            "dir_logs": self.dir_logs,
            "dir_setup": self.dir_setup,
            "dir_expr": self.dir_expr,
            "dir_output": self.dir_output,
        }

        localization_list = bug_info[self.key_localization]
        diff_list = []
        status = 0
        prog_lang = bug_info.get(self.key_language)
        # TODO: this is a hack to temporarily disable internal validation
        hack_command = 'sed -i "126d" /home/aixcc-repair/api/sft_repair.py'
        self.run_command(hack_command)
        for localization in localization_list:
            fix_file = localization[self.key_fix_file]
            dir_src = join(self.dir_expr, "src")
            if prog_lang == "c":
                rel_src_path = fix_file.replace(dir_src + "/", "")
            elif prog_lang == "java":
                java_src_path = bug_info.get(self.key_dir_source)
                fix_class_name = fix_file
                class_path = fix_class_name.replace(".", "/")
                rel_src_path = f"{java_src_path}/{class_path}.java"
            else:
                rel_src_path = fix_file
            fix_lines = [int(x) for x in localization[self.key_fix_lines]]
            for line_num in fix_lines:
                bug_info[self.key_fix_file] = rel_src_path
                bug_info[self.key_fix_lines] = [line_num]
                bug_info_encoded = base64.b64encode(
                    json.dumps(bug_info).encode()
                ).decode()
                tool_info_encoded = base64.b64encode(
                    json.dumps(tool_info).encode()
                ).decode()
                timeout_h = str(task_config_info[self.key_timeout])
                repair_command = f"bash -c 'cd /home/aixcc-repair/api && python sft_repair.py {bug_info_encoded} {tool_info_encoded}'"
                repair_command = f"timeout -k 5m {timeout_h}h {repair_command} "
                self.timestamp_log_start()
                status = self.run_command(
                    repair_command,
                    self.log_output_path,
                    dir_path="/home/aixcc-repair/",
                )
                result_json_path = f"{self.dir_output}/result.json"
                self.run_command(f"cp /home/result.json {result_json_path}")
                result_json = self.read_json(result_json_path)
                abs_src_path = os.path.join(self.dir_expr, "src", rel_src_path)
                if not isinstance(result_json, List):
                    result_json = []
                for result in result_json:
                    patched_line = result["patch"]
                    src_diff = self.generate_diff(abs_src_path, line_num, patched_line)
                    diff_list.append(src_diff)
        patch_directory = join(self.dir_output, "patches")
        self.write_patch_files(patch_directory, diff_list)
        self.process_status(status)
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("[warning] no log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        self.stats.patch_stats.generated = len(
            self.list_dir(join(self.dir_output, "patches"))
        )

        return self.stats
