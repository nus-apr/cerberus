import abc
import os
import shutil
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import container
from app.core import definitions
from app.core import utilities
from app.core.task.stats.CompositeToolStats import CompositeToolStats
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.core.utilities import error_exit
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractCompositeTool(AbstractTool):
    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_dir_class = definitions.KEY_CLASS_DIRECTORY
    key_dir_source = definitions.KEY_SOURCE_DIRECTORY
    key_dir_tests = definitions.KEY_TEST_DIRECTORY
    key_dir_test_class = definitions.KEY_TEST_CLASS_DIRECTORY
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES
    key_composite_sequence = definitions.KEY_COMPOSITE_SEQUENCE

    stats: CompositeToolStats

    def __init__(self, tool_name):
        self.stats = CompositeToolStats()
        super().__init__(tool_name)

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_patches = dir_info["patches"]
        if os.path.isdir(base_dir_patches):
            dir_patches = join(base_dir_patches, self.name)
            if os.path.isdir(dir_patches):
                shutil.rmtree(dir_patches)
            os.makedirs(dir_patches)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_patches}"
                )
            else:
                save_command = "cp -rf {} {};".format(self.dir_output, f"{dir_patches}")
                utilities.execute_command(save_command)

        super().save_artifacts(dir_info)
        return

    def analyse_output(
        self, dir_info, bug_id: str, fail_list: List[str]
    ) -> CompositeToolStats:
        """
        composite tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """

        # if self.is_dir(self.dir_patch):
        #    self.stats.patch_stats.size = len(self.list_dir(self.dir_patch))

        return self.stats

    def run_composite(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info: Dict[str, Any],
        composite_config_info: Dict[str, Any],
        container_config_info: Dict[str, Any],
        run_index: str,
        hash: str,
    ) -> None:
        self.emit_normal("validating experiment subject")
        utilities.check_space()
        self.pre_process()
        self.emit_normal("executing validate command")
        task_conf_id = composite_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.dir_patch = join(self.dir_output, "patches")
        log_file_name = "{}-{}-{}-output.log".format(
            task_conf_id, self.name.lower(), bug_id
        )
        filtered_bug_info = dict()
        interested_keys = [
            self.key_id,
            self.key_bug_id,
            self.key_subject,
            self.key_benchmark,
            definitions.KEY_COUNT_NEG,
            definitions.KEY_COUNT_POS,
        ]
        for k in interested_keys:
            filtered_bug_info[k] = bug_info[k]
        composite_config_info["container-id"] = self.container_id
        self.stats.bug_info = filtered_bug_info
        self.stats.config_info = composite_config_info
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return

    def print_stats(self) -> None:
        self.stats.write(self.emit_highlight, "\t")

    def emit_normal(self, message):
        super().emit_normal("composite-tool", self.name, message)

    def emit_warning(self, message):
        super().emit_warning("composite-tool", self.name, message)

    def emit_error(self, message):
        super().emit_error("composite-tool", self.name, message)

    def emit_highlight(self, message):
        super().emit_highlight("composite-tool", self.name, message)

    def emit_success(self, message):
        super().emit_success("composite-tool", self.name, message)

    def emit_debug(self, message):
        super().emit_debug("composite-tool", self.name, message)
