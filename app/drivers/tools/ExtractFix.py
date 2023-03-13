import os
from os import path

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class ExtractFix(AbstractTool):
    bug_conversion_table = {
        "Buffer Overflow": "buffer_overflow",
        "Use after Free": "buffer_overflow",
        "Integer Overflow": "integer_overflow",
        "Data Type Overflow": "integer_overflow",
        "Null Pointer Dereference": "null_pointer",
        "Divide by Zero": "divide_by_0",
        "API Assertion": "assertion_failure",
        "API Specific": "api_specific",
    }

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ExtractFix, self).__init__(self.name)
        self.dir_root = "/ExtractFix/"
        self.image_name = "gaoxiang9430/extractfix:demo"

    def repair(self, bug_info, config_info):
        super(ExtractFix, self).repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        if values.only_instrument:
            return

        # modify the output directory as it depends on the experiment
        self.dir_output = path.join(self.dir_expr, "result")
        self.dir_logs = path.join(self.dir_expr, "logs")

        dir_extractfix_exist = self.is_dir(self.dir_root)
        if not dir_extractfix_exist:
            emitter.error(
                "[Exception] ExtractFix repo is not at the expected location. "
                "Please double check whether we are in ExtractFix container."
            )
            error_exit("Unhandled exception")
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        # prepare the config file
        parameters = self.create_parameters(bug_info)

        # start running
        self.timestamp_log_start()
        extractfix_command = "bash -c 'source /ExtractFix/setup.sh && timeout -k 5m {}h ./ExtractFix.py {} {} >> {}'".format(
            timeout_h, parameters, additional_tool_param, self.log_output_path
        )
        status = self.run_command(
            extractfix_command,
            log_file_path=self.log_output_path,
            dir_path=path.join(self.dir_root, "build"),
        )
        self.timestamp_log_end()

        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def create_parameters(self, experiment_info):
        """
        Construct the parametes for ExtractFix.
        """

        # (1) source-dir
        line_source_dir = "-s " + (
            "/libtiff-3186"
            if experiment_info[definitions.KEY_BUG_ID] == "CVE-2016-3186"
            else "/coreutils-25003"
            if experiment_info[definitions.KEY_BUG_ID] == "gnubug-25003"
            else self.dir_expr
        )

        # (2) test file
        # dir_tests = "/".join([self.dir_setup, "tests"])
        # tests_list = self.list_dir(dir_tests)
        # if not tests_list:
        #     emitter.error(
        #         "[Exception] there needs to be at least 1 exploit (failing) input!"
        #     )
        #     error_exit("Unhandled Exception")
        # Currently we assume that the test cases are copied, this can be simplified by using the tests_lsit above
        test_case = "-t " + (
            experiment_info[definitions.KEY_EXPLOIT_LIST][0]
            if len(experiment_info[definitions.KEY_EXPLOIT_LIST]) != 0
            else "dummy"
        )

        # (3) driver
        driver = "-c driver"

        # (4) bug type
        bug_type = "-b " + (
            "api_specific"
            if experiment_info[definitions.KEY_BUG_ID] == "CVE-2016-3186"
            or experiment_info[definitions.KEY_BUG_ID] == "gnubug-25003"
            else ExtractFix.bug_conversion_table[
                experiment_info[definitions.KEY_BUG_TYPE]
            ]
        )

        if bug_type == "-b ":
            utilities.error_exit(
                "Bug {} does not have {} field to indicate the type".format(
                    experiment_info[definitions.KEY_BUG_ID], definitions.KEY_BUG_TYPE
                )
            )

        # (5) buggy program
        program = "-n " + experiment_info[definitions.KEY_BINARY_PATH].split("/")[-1]

        # (6) verbose?
        verbose = "-v"

        return " ".join(
            [line_source_dir, test_case, driver, bug_type, program, verbose]
        )

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        self.run_command(
            "cp -r result0 result/", dir_path=path.join(self.dir_root, self.dir_expr)
        )
        self.run_command(
            "cp -r result1 result/", dir_path=path.join(self.dir_root, self.dir_expr)
        )
        super().save_artifacts(dir_info)
        return

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

        is_error = False
        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self._space.generated = len(
            [name for name in list_output_dir if "patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "successfully generate patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        self._error.is_error = is_error
        return self._space, self._time, self._error
