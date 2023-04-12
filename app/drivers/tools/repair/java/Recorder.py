import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Recorder(AbstractRepairTool):
    """
    Requirements for this tool:
    15 GB of VRAM, at most 7.0 CUDA (e.g. Nvidia V100) compute and 20 GB of RAM
    """

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Recorder, self).__init__(self.name)
        self.image_name = "zqh111/recoder:interface"
        self.bug_name = ""

    def run_repair(self, bug_info, config_info):
        super(Recorder, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])

        if not values.use_gpu:
            utilities.error_exit("Cannot run Recorder without a GPU")

        self.bug_name = "{}-{}".format(
            bug_info[definitions.KEY_SUBJECT],
            bug_info[definitions.KEY_BUG_ID],
        )
        # generate patches
        self.timestamp_log_start()
        recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 testDefect4jv21.py {}-{}'".format(  # currently supporting only defects4j
            timeout_h,
            bug_info[definitions.KEY_SUBJECT],
            bug_info[definitions.KEY_BUG_ID],
        )
        status = self.run_command(
            recorder_command, self.log_output_path, "/root/Repair/"
        )

        recorder_command = "bash -c 'export PATH=$PATH:/root/defects4j/framework/bin && timeout -k 5m {}h python3 repair.py {}-{}'".format(
            timeout_h,
            bug_info[definitions.KEY_SUBJECT],
            bug_info[definitions.KEY_BUG_ID],
        )

        status = self.run_command(
            recorder_command,
            self.log_output_path,
            "/root/Repair/",
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
        self._space.generated = 1

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
            self.run_command(
                "cp /root/Repair/patches/{}patch.txt /output/".format(self.bug_name)
            )
            self._space.generated = 1
            self._space.enumerations = 1
            self._space.plausible = 1
            self._space.non_compilable = 0

        return self._space, self._time, self._error
