import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SequenceR(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/sequencer:latest"

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

        # The zimin/sequencer container has a bug which can only be found after a removal
        # of a /dev/null pipe in sequencer-predict
        self.run_command(
            "sed -i '183s/1\\s*-\\s*/~/' ./onmt/modules/global_attention.py",
            "/dev/null",
            "/SequenceR/src/lib/OpenNMT-py",
        )

        if (
            self.key_localization not in bug_info
            or len(bug_info[self.key_localization]) < 1
        ):
            self.update_experiment_status("No fault localization info given")
            self.error_exit(
                "Cannot apply SequenceR on an experiment with no given buggy file or line"
            )

        localization_target = bug_info[self.key_localization][0]

        # generate patches
        self.timestamp_log_start()
        file = (
            join(
                bug_info[self.key_dir_source],
                localization_target[self.key_fix_file].replace(".", "/"),
            )
            + ".java"
        )  # construct the file's path

        # Optional - update the status of the experiment to allow for tracking of intermediate states in parallel mode
        self.update_experiment_status("Generatng predictions")

        sequencer_command = "timeout -k 5m {}h ./sequencer-predict.sh --model=/SequenceR/model/model.pt --buggy_file={} --buggy_line={} --beam_size=100 --output={}".format(
            timeout_h,
            join(self.dir_expr, "src", file),
            localization_target[self.key_fix_lines][0],
            join(self.dir_output, "patches"),
        )
        status = self.run_command(
            sequencer_command, self.log_output_path, "/SequenceR/src"
        )

        # Optional - update the status of the experiment to allow for tracking of intermediate states in parallel mode
        self.update_experiment_status("Validating predictions")

        sequencer_command = (
            "timeout -k 5m {3}h python3 validatePatch.py {0} {1} {2}".format(
                join(self.dir_output, "patches"),
                join(
                    self.dir_expr,
                    "src",
                ),
                join(self.dir_expr, "src", file),
                timeout_h,
            )
        )

        status = self.run_command(
            sequencer_command,
            self.log_output_path,
            "/SequenceR/src/Defects4J_Experiment",
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

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")

        if not self.stats.error_stats.is_error:
            patch_space = len(
                self.list_dir("{}/patches".format(self.dir_output), regex=".*java")
            )
            self.stats.patch_stats.generated = patch_space
            self.stats.patch_stats.enumerations = patch_space
            self.stats.patch_stats.plausible = len(
                self.list_dir(
                    "{}/patches".format(self.dir_output),
                    regex=".*/[0-9]+_passed/.*java",
                )
            )
            self.stats.patch_stats.non_compilable = len(
                self.list_dir(
                    "{}/patches".format(self.dir_output), regex=".*/[0-9]+/.*java"
                )
            )

        return self.stats
