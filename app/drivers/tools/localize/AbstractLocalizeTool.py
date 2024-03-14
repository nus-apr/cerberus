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
from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractLocalizeTool(AbstractTool):
    key_bin_path = definitions.KEY_BINARY_PATH
    key_crash_cmd = definitions.KEY_CRASH_CMD
    key_exploit_list = definitions.KEY_EXPLOIT_LIST
    key_failing_test_identifiers = definitions.KEY_FAILING_TEST
    key_passing_test_identifiers = definitions.KEY_PASSING_TEST
    key_dir_class = definitions.KEY_CLASS_DIRECTORY
    key_dir_source = definitions.KEY_SOURCE_DIRECTORY
    key_dir_tests = definitions.KEY_TEST_DIRECTORY
    key_dir_test_class = definitions.KEY_TEST_CLASS_DIRECTORY
    key_config_timeout_test = definitions.KEY_CONFIG_TIMEOUT_TESTCASE
    key_dependencies = definitions.KEY_DEPENDENCIES
    key_fl_formula = definitions.KEY_FL_FORMULA
    stats: LocalizeToolStats

    def __init__(self, tool_name):
        self.stats = LocalizeToolStats()
        super().__init__(tool_name)

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        base_dir_localization = dir_info["localization"]
        if os.path.isdir(base_dir_localization):
            dir_localization = join(base_dir_localization, self.name)
            if os.path.isdir(dir_localization):
                shutil.rmtree(dir_localization)
            os.makedirs(dir_localization)
            if self.container_id:
                container.copy_file_from_container(
                    self.container_id, self.dir_output, f"{dir_localization}"
                )
            else:
                save_command = "cp -rf {} {};".format(
                    self.dir_output, f"{dir_localization}"
                )
                utilities.execute_command(save_command)

        super().save_artifacts(dir_info)
        return

    def instrument(self, bug_info: Dict[str, Any]) -> None:
        """instrumentation for the experiment as needed by the tool"""
        if not self.is_file(join(self.dir_inst, "instrument.sh")):
            return
        self.emit_normal("running instrumentation script")
        bug_id = bug_info[definitions.KEY_BUG_ID]
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        buggy_file = bug_info.get(self.key_localization, [{}])[0].get(
            definitions.KEY_FIX_FILE, ""
        )
        self.log_instrument_path = join(
            self.dir_logs,
            "{}-{}-{}-instrument.log".format(task_conf_id, self.name, bug_id),
        )
        time = datetime.now()
        command_str = "bash instrument.sh {} {}".format(self.dir_base_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        self.emit_debug(
            "\t\t\t instrumentation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of {}; exit code {}".format(
                    self.name, str(status)
                )
            )
        return

    def analyse_output(
        self, dir_info, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.fix_loc_stats.plausible
            self.stats.fix_loc_stats.size
            self.stats.fix_loc_stats.enumerations
            self.stats.fix_loc_stats.generated

        """

        return self.stats

    def run_localization(
        self, bug_info: Dict[str, Any], localization_config_info: Dict[str, Any]
    ) -> None:
        self.emit_normal("running fix localization on subject")
        utilities.check_space()
        self.pre_process()
        self.instrument(bug_info)
        self.emit_normal("executing localization command")
        task_conf_id = localization_config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        self.dir_localization = join(self.dir_output, "localization")
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
        localization_config_info["container-id"] = self.container_id
        self.stats.bug_info = filtered_bug_info
        self.stats.config_info = localization_config_info
        self.log_output_path = os.path.join(self.dir_logs, log_file_name)
        self.run_command("mkdir {}".format(self.dir_output), "dev/null", "/")
        return

    def print_stats(self) -> None:
        self.stats.write(self.emit_highlight, "\t")

    def emit_normal(self, message):
        super().emit_normal(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_warning(self, message):
        super().emit_warning(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_error(self, message):
        super().emit_error(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_highlight(self, message):
        super().emit_highlight(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_success(self, message):
        super().emit_success(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )

    def emit_debug(self, message):
        super().emit_debug(
            "localize-tool",
            self.name + (("-" + self.tool_tag) if self.tool_tag else ""),
            message,
        )
