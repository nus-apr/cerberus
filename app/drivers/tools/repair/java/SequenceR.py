import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SequenceR(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "zimin/sequencer:1.0"

    def run_repair(self, bug_info, repair_config_info):
        super(SequenceR, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(repair_config_info[self.key_timeout])

        # The zimin/sequencer container has a bug which can only be found after be found after a removal
        # of a /dev/null pipe in sequencer-predict
        self.run_command(
            "sed -i '183s/1\\s*-\\s*/~/' ./onmt/modules/global_attention.py",
            "/dev/null",
            "/SequenceR/src/lib/OpenNMT-py",
        )

        if bug_info[self.key_fix_file] == "" or len(bug_info[self.key_fix_lines]) < 1:
            self.error_exit(
                "Cannot apply SequenceR on an experiment with no given buggy file or line"
            )

        # generate patches
        self.timestamp_log_start()
        file = (
            join(
                bug_info[self.key_dir_source],
                bug_info[self.key_fix_file].replace(".", "/"),
            )
            + ".java"
        )  # construct the file's path

        # Optional - update the status of the experiment to allow for tracking of intermediate states in parallel mode
        self.update_experiment_status("Generatng predictions")

        sequencer_command = "timeout -k 5m {}h ./sequencer-predict.sh --buggy_file={} --buggy_line={} --beam_size=100 --output={}".format(
            timeout_h,
            join(self.dir_expr, "src", file),
            bug_info[self.key_fix_lines][0],
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

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(self, dir_info, bug_id, fail_list):
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

        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patches_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

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
            patch_space = self.list_dir("/output/patches")
            self.stats.patches_stats.generated = len(patch_space)
            self.stats.patches_stats.enumerations = len(patch_space)
            self.stats.patches_stats.plausible = len(
                list(filter(lambda x: "passed" in x, patch_space))
            )
            self.stats.patches_stats.non_compilable = (
                self.stats.patches_stats.generated
                - self.stats.patches_stats.enumerations
            )

        return self.stats
