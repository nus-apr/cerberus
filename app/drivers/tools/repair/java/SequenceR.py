import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class SequenceR(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(SequenceR, self).__init__(self.name)
        self.image_name = "zimin/sequencer:1.0"

    def run_repair(self, bug_info, config_info):
        super(SequenceR, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])

        # The zimin/sequencer container has a bug which can only be found after be found after a removal
        # of a /dev/null pipe in sequencer-predict
        self.run_command(
            "sed -i '183s/1\\s*-\\s*/~/' ./onmt/modules/global_attention.py",
            "/dev/null",
            "/SequenceR/src/lib/OpenNMT-py",
        )

        if (
            bug_info[definitions.KEY_FIX_FILE] == ""
            or len(bug_info[definitions.KEY_FIX_LINES]) < 1
        ):
            utilities.error_exit(
                "Cannot apply SequenceR on an experiment with no given buggy file or line"
            )

        # generate patches
        self.timestamp_log_start()
        file = (
            join(
                bug_info[definitions.KEY_SOURCE_DIRECTORY],
                bug_info[definitions.KEY_FIX_FILE].replace(".", "/"),
            )
            + ".java"
        )  # construct the file's path
        sequencer_command = "timeout -v -k 5m {}h ./sequencer-predict.sh --buggy_file={} --buggy_line={} --beam_size=100 --output={}".format(
            timeout_h,
            join(self.dir_expr, "src", file),
            bug_info[definitions.KEY_FIX_LINES][0],
            join(self.dir_output, "patches"),
        )
        status = self.run_command(
            sequencer_command, self.log_output_path, "/SequenceR/src"
        )

        sequencer_command = (
            "timeout -v -k 5m {3}h python3 validatePatch.py {0} {1} {2}".format(
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
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

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

            self._space.non_compilable
            self._space.plausible
            self._space.size
            self._space.enumerations
            self._space.generated

            self._time.total_validation
            self._time.total_build
            self._time.timestamp_compilation
            self._time.timestamp_validation
            self._time.timestamp_plausible
        """
        emitter.normal("\t\t\t analysing output of " + self.name)

        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self._space.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")

        if not self._error.is_error:
            patch_space = self.list_dir("/output/patches")
            self._space.generated = len(patch_space)
            self._space.enumerations = len(patch_space)
            self._space.plausible = len(
                list(filter(lambda x: "passed" in x, patch_space))
            )
            self._space.non_compilable = (
                self._space.generated - self._space.enumerations
            )

        return self._space, self._time, self._error
