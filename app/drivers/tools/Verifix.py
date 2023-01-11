import os
from os.path import join

from app.core import definitions, values, emitter
from app.drivers.tools.AbstractTool import AbstractTool


class Verifix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Verifix, self).__init__(self.name)
        self.image_name = "mirchevmp/verifix:latest"

    def repair(self, bug_info, config_info):
        super(Verifix, self).repair(bug_info, config_info)
        """ 
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output 
        """

        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])

        # start running
        self.timestamp_log()
        vulnfix_command = "timeout -k 5m {}h python3 -m main -m repair -tool verifix -debug {} -pc {} -pi {} -tc {}".format(
            timeout_h,
            "true" if values.debug else "false",
            join(
                self.dir_setup,
                bug_info[definitions.KEY_FIX_FILE].replace("buggy", "correct"),
            ),
            join(self.dir_setup, bug_info[definitions.KEY_FIX_FILE]),
            join(self.dir_expr, "base", "test"),
        )
        status = self.run_command(vulnfix_command, self.log_output_path, "/Verifix")

        if status != 0:
            self._error.is_error = True
            emitter.warning(
                "\t\t\t[warning] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))

        self.timestamp_log()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artefacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artefacts(dir_info)

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
            emitter.warning("\t\t\t[warning] no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")

        if not self._error.is_error:
            self._space.plausible = 1
            self._space.enumerations = 1

        return self._space, self._time, self._error
