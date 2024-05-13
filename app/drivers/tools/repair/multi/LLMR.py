import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import definitions
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class LLMR(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/llmr"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(task_config_info[self.key_timeout])
        # Any communication based model works
        model = task_config_info.get("model", "gpt-4")
        params = task_config_info.get(self.key_tool_params, "")

        passing_test_identifiers = ",".join(bug_info[self.key_passing_test_identifiers])
        failing_test_identifiers = ",".join(bug_info[self.key_failing_test_identifiers])

        self.run_command("mkdir -p {}".format(join(self.dir_output, "patches")))

        if (
            task_config_info["fault_location"] == "auto"
            and self.key_localization in bug_info
        ):
            fl_info = []
            for location in bug_info[self.key_localization]:
                file = location[self.key_fix_file]
                if bug_info[self.key_language] == "java" and not file.endswith(".java"):
                    file = f"src/main/java/{file.replace('.', '/')}.java"
                locations = location[self.key_fix_lines]
                for line in locations:
                    fl_info.append(f"{file}::{line},1\n")

            self.emit_debug(f"File localization info: {fl_info}")
            fl_path = join(self.dir_output, "fl_data.txt")
            self.write_file(fl_info, fl_path)
            fl = f"-fl-data {fl_path}"
        else:
            fl = "-do-fl"

        language = (
            "-lang {}".format(bug_info[self.key_language])
            if self.key_language in bug_info
            else ""
        )

        bug_description = (
            "-description {}".format(join(self.dir_setup, bug_info["bug_description"]))
            if "bug_description" in bug_info
            else ""
        )
        reference_file = (
            "-reference {}".format(bug_info[definitions.KEY_REFERENCE_FILE])
            if definitions.KEY_REFERENCE_FILE in bug_info
            else ""
        )

        env = {}
        java_version = bug_info.get(self.key_java_version, 8)
        if int(java_version) <= 7:
            java_version = 8
        env["JAVA_HOME"] = f"/usr/lib/jvm/java-{java_version}-openjdk-amd64/"

        if self.key_build_script in bug_info:
            # Build it once to have things prepared
            self.run_command(
                "bash {}".format(bug_info.get(self.key_build_script)),
                dir_path=self.dir_setup,
                env=env,
            )

        openai_token = self.api_keys.get(self.key_openai_token, None)
        if not openai_token:
            self.error_exit(f"{self.name} requires at least one API key for OpenAI")
        # start running
        self.timestamp_log_start()
        llmr_command = "timeout -k 5m {timeout_h}h python3 /tool/repair.py {fl} --project-path {project_path} -model {model} {reference_file} {bug_description} {build_script} -output {output_loc} -patches {patch_count} -test {test_script} {binary_path} {passing_test_identifiers} {failing_test_identifiers} {debug} {language} -key {openai_token} {params}".format(
            timeout_h=timeout_h,
            patch_count=5,
            project_path=join(self.dir_expr, "src"),
            build_script=(
                "-build {}".format(
                    join(self.dir_setup, bug_info[self.key_build_script])
                )
                if (
                    self.key_build_script in bug_info
                    and bug_info[self.key_build_script] != ""
                )
                else ""
            ),
            output_loc=self.dir_output,
            test_script=join(self.dir_setup, bug_info[self.key_test_script]),
            model=model,
            passing_test_identifiers=(
                "-passing-tests {}".format(passing_test_identifiers)
                if passing_test_identifiers != ""
                else " "
            ),
            failing_test_identifiers=(
                "-failing-tests {}".format(failing_test_identifiers)
                if failing_test_identifiers != ""
                else " "
            ),
            binary_path=(
                "-binary-loc {}".format(bug_info[self.key_bin_path])
                if self.key_bin_path in bug_info
                else " "
            ),
            debug="-d" if self.is_debug else "",
            reference_file=reference_file,
            bug_description=bug_description,
            language=language,
            fl=fl,
            params=params,
            openai_token=openai_token,
        )
        status = self.run_command(
            llmr_command, self.log_output_path, join(self.dir_expr, "src"), env=env
        )

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
        # remove traces that are not necessary
        remove_command = (
            f"rm -rf {self.dir_output}/failing_traces {self.dir_output}/passing_traces "
        )
        self.exec_command(remove_command)
        super().save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        self.emit_normal("reading output")

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_patch)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")

            for line in log_lines:
                if re.match("Patch .* is Plausible", line):
                    self.stats.patch_stats.plausible += 1
                if re.match("response", line):
                    self.stats.patch_stats.generated += 1
                if re.match("does not compile", line):
                    self.stats.patch_stats.non_compilable += 1

        return self.stats
