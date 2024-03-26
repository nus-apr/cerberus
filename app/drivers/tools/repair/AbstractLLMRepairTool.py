import difflib
import os
from os.path import join
from pathlib import Path
from typing import Any
from typing import Dict
from typing import List
from typing import Tuple

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractLLMTool import AbstractLLMTool


class AbstractLLMRepairTool(AbstractLLMTool):
    stats: RepairToolStats

    def __init__(self, tool_name: str) -> None:
        self.stats = RepairToolStats()
        self.tool_type = "repair-tool"
        self.dir_patch = ""
        super().__init__(tool_name)

    def generate_diff(self, src_path: str, line_number: int, patch_line: str) -> str:
        buggy_lines = self.read_file(src_path, encoding="ISO-8859-1")
        fixed_lines = buggy_lines.copy()
        fixed_lines[line_number - 1] = f"{patch_line}"
        source_file = Path(self.dir_expr, "src", src_path).absolute()
        dir_src = os.path.join(self.dir_expr, "src")
        src_diff = "".join(
            difflib.unified_diff(
                buggy_lines,
                fixed_lines,
                fromfile=str(source_file.relative_to(dir_src)),
                tofile=str(source_file.relative_to(dir_src)),
            )
        )
        return src_diff

    def write_patch_files(self, dir_patch: str, diff_list: List[str]) -> None:
        mkdir_cmd = f"mkdir -p {dir_patch}"
        self.exec_command(mkdir_cmd)
        for i, patch in enumerate(diff_list):
            patch_file_path = os.path.join(dir_patch, f"{i}.patch")
            self.write_file(patch, patch_file_path)

    def create_prompts(
        self, src_locations: List[Tuple[str, int]], bug_info: Dict[str, Any]
    ) -> List[str]:
        prompt_list = []
        prog_lang = bug_info.get(self.key_language, "")
        bug_type = bug_info.get(self.key_bug_type, "")
        for rel_src_path, line_number in src_locations:
            abs_src_path = os.path.join(self.dir_expr, "src", rel_src_path)
            prompt = self.generate_prompt(
                abs_src_path, line_number, bug_type, prog_lang
            )
            prompt_list.append(prompt)
        return prompt_list

    def invoke_advanced(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info: Dict[str, Any],
        task_config_info: Dict[str, Any],
        container_config_info: Dict[str, Any],
        run_index: str,
        hash: str,
    ) -> None:
        super().invoke_advanced(
            dir_info,
            benchmark,
            bug_info,
            task_config_info,
            container_config_info,
            run_index,
            hash,
        )
        self.write_json(
            [{"patches_dir": join(self.dir_output, "patches")}],
            join(self.dir_output, "meta-data.json"),
        )
