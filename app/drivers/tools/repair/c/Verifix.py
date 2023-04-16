import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Verifix(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/verifix:latest"

    def run_repair(self, bug_info, config_info):
        super(Verifix, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(config_info[self.key_test_timeout])

        # start running
        self.timestamp_log_start()
        vulnfix_command = "timeout -k 5m {}h python3 -m main -m repair -tool verifix -debug {} -pc {} -pi {} -tc {}".format(
            timeout_h,
            "true" if self.is_debug else "false",
            join(
                self.dir_setup,
                bug_info[definitions.KEY_FIX_FILE].replace("buggy", "correct"),
            ),
            join(self.dir_setup, bug_info[definitions.KEY_FIX_FILE]),
            join(self.dir_expr, "base", "test"),
        )
        status = self.run_command(vulnfix_command, self.log_output_path, "/Verifix")

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
        self.emit_normal("reading output")

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self._space.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")

        if not self._error.is_error:
            self._space.plausible = 1
            self._space.enumerations = 1

        return self._space, self._time, self._error
