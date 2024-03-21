import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class ZAP(AbstractFuzzTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "jarvx/zap_jenkins:3.0"

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> FuzzToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """

        return self.stats

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        self.emit_normal("executing fuzz command")

        timeout = int(float(task_config_info[self.key_timeout]) * 60)

        self.timestamp_log_start()

        initial_corpus = join(self.dir_setup, self.name, "initial-corpus")

        # timeout is the number of mins # timeout is the number of mins
        fuzz_command = f"/zap/zap-full-scan.py -t http://127.0.0.1:8080/ -m {timeout}"

        status = self.run_command(
            fuzz_command, self.log_output_path, join(self.dir_expr, "src")
        )

        self.process_status(status)

        self.timestamp_log_end()
