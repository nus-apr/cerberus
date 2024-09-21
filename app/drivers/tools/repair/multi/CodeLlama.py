import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractLLMRepairTool import AbstractLLMRepairTool


class CodeLlama(AbstractLLMRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(CodeLlama, self).__init__(self.name)
        self.image_name = "rshariffdeen/codellama:latest"
        self.hash_digest = (
            "sha256:124ede08ec7379305e25c2a8632bf1d87c817a333b17e5f7ddf927240cd7e251"
        )

    def generate_prompt(
        self,
        source_file_path: str,
        line_number: int,
        bug_type: str,
        prog_lang: str,
    ) -> str:

        allowed_node_types = ["MethodDeclaration", "ConstructorDeclaration"]
        buggy_method = self.load_origin_code_node(
            source_file_path,
            line_number,
            prog_lang,
            allowed_node_types,
        )[0]

        # Step 3: Get the buggy code with line numbers
        # If the ast nodes are not of the correct type, then we have a whole-function removal/addition
        buggy_code = (
            self.find_code(
                source_file_path,
                [i for i in range(buggy_method.start_pos, buggy_method.end_pos + 1)],
            )
            if buggy_method is not None
            else ""
        ).strip()

        if buggy_code == "":
            return ""

        # Step 4: Iterate over the buggy code to generate the prompt
        prompt = f"Following {prog_lang} code has a {bug_type}\n"
        buggy_code_lines = buggy_code.splitlines(keepends=True)
        for i, line in enumerate(
            range(buggy_method.start_pos, buggy_method.end_pos + 1)
        ):
            if str(line) == str(line_number):
                prompt += f"// buggy lines start:\n"
                prompt += buggy_code_lines[i]
                prompt += f"// buggy lines end\n"
            else:
                prompt += buggy_code_lines[i]
        return prompt

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """
        gpu_list = task_config_info.get(self.key_gpus)
        if not isinstance(gpu_list, List):
            gpu_list = []
        if len(gpu_list) == 0:
            self.error_exit(f"{self.name} requires GPUs")

        localization_list = bug_info.get(self.key_localization, [])
        if not localization_list:
            self.error_exit(f"{self.name} requires localization information")
        patch_directory = join(self.dir_output, "patches")
        fix_loc_list = []
        for _l in localization_list:
            src_path = _l.get(self.key_fix_file)
            line_numbers = _l.get(self.key_fix_lines)
            for _n in line_numbers:
                fix_loc_list.append((str(src_path), int(_n)))

        # generate repair prompts for each location
        prompt_list = self.create_prompts(fix_loc_list, bug_info)

        # write prompt to json file
        prompt_json_path = join(self.dir_setup, f"{self.name}.json")
        self.write_json(prompt_list, prompt_json_path)

        # Invoke LLM interface with the prompts
        prog_lang = bug_info.get(self.key_language)
        result_json_path = join(self.dir_output, "responses.json")
        maximum_patches = 5
        invoke_command = (
            f"torchrun --nproc_per_node 1 cerberus.py     "
            f"--ckpt_dir CodeLlama-7b-Instruct/     "
            f"--tokenizer_path CodeLlama-7b-Instruct/tokenizer.model     "
            f"--max_seq_len 512 "
            f"--max_batch_size 4 "
            f"--num_responses {maximum_patches} "
            f"--prog_language {prog_lang} "
            f"--prompt_json_path {prompt_json_path} "
            f"--result_json_path {result_json_path}"
        )
        self.timestamp_log_start()
        timeout = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]
        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        repair_command = f"timeout -k 5m {timeout}h {invoke_command} "
        dir_src = join(self.dir_expr, "src")
        if additional_tool_param:
            repair_command = repair_command + " " + additional_tool_param
        status = self.run_command(
            repair_command, self.log_output_path, "/opt/codellama"
        )

        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()
        if not self.is_file(result_json_path):
            self.emit_error("\t\tModel did not generate a response")
            return
        result_list = self.read_json(result_json_path)
        if not isinstance(result_list, List):
            self.error_exit("expected result json to provide a list")
        diff_list = []
        for result in result_list:
            _prompt, _response = result
            prompt_index = prompt_list.index(_prompt)
            fix_loc = fix_loc_list[prompt_index]
            rel_src_path, line_number = fix_loc
            abs_src_path = os.path.join(self.dir_expr, "src", rel_src_path)
            patch_list = _response.split("```")
            for i, patch in enumerate(patch_list):
                if i % 2 != 0:
                    src_diff = self.generate_diff(abs_src_path, line_number, patch)
                    diff_list.append(src_diff)
        self.write_patch_files(patch_directory, diff_list)

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
