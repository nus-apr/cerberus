import os
from os.path import basename
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class TBar(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(TBar, self).__init__(self.name)
        self.tbar_root_dir = "/TBar"
        self.image_name = "mirchevmp/tbar-cerberus:latest"

    def run_repair(self, bug_info, config_info):
        super(TBar, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """
        if values.only_instrument:
            return

        dir_tbar_exist = self.is_dir(self.tbar_root_dir)
        if not dir_tbar_exist:
            emitter.error(
                "[Exception] TBar repo is not at the expected location. "
                "Please double check whether we are in TBar container."
            )
            error_exit("Unhandled exception")
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]

        if self.container_id:
            # Ensure that the container has git setup
            self.run_command(
                "bash -c 'git config --global user.email cerberus@nus-apr.com && git config --global user.name CERBERUS'",
                dir_path=join(self.dir_expr, "src"),
            )

        # Ensure that there is a repo set up for the experiment and clean of any non-staged data
        self.run_command(
            "bash -c 'git init && git add . && git commit -m \"TEMP COMMIT\"'",
            dir_path=join(self.dir_expr, "src"),
        )

        # prepare the required parameters
        parameters = self.create_parameters(bug_info)

        command = (
            'mvn compile exec:java -Dexec.mainClass="edu.lu.uni.serval.tbar.main.Main"'
        )
        args = (
            "FAILING_TESTS='{}' ".format(
                " ".join(bug_info[definitions.KEY_FAILING_TEST])
            )
            + "CLASS_DIRECTORY={} ".format(bug_info[definitions.KEY_CLASS_DIRECTORY])
            + "TEST_CLASS_DIRECTORY={} ".format(
                bug_info[definitions.KEY_TEST_CLASS_DIRECTORY]
            )
            + "SOURCE_DIRECTORY={} ".format(bug_info[definitions.KEY_SOURCE_DIRECTORY])
            + "TEST_SOURCE_DIRECTORY={} ".format(
                bug_info[definitions.KEY_TEST_DIRECTORY]
            )
        )

        # start running
        self.timestamp_log_start()
        tbar_command = (
            "bash -c '{4} timeout -k 5m {0}h {1} -Dexec.args=\"{2} {3}\"'".format(
                timeout_h, command, parameters, additional_tool_param, args
            )
        )

        status = self.run_command(
            tbar_command,
            log_file_path=self.log_output_path,
            dir_path=self.tbar_root_dir,
        )

        self.process_status(status)

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def create_parameters(self, experiment_info):
        """
        Formats of execution cmds:
            * ./PerfectFLTBarRunner.sh <Bug_Data_Path> <Bug_ID> <defects4j_Home> <Generate_All_Possible_Patches_Bool>
            * ./NormalFLTBarRunner.sh <Bug_Data_Path> <Bug_ID> <defects4j_Home>

        Examples:
            * ./PerfectFLTBarRunner.sh D4J/projects/ Chart_8 D4J/defects4j/ false
            * ./NormalFLTBarRunner.sh D4J/projects/ Chart_8 D4J/defects4j/
        """

        defects4j_home = "/defects4j/"
        bug_id_str = "{0}_{1}".format(
            experiment_info[definitions.KEY_SUBJECT],
            experiment_info[definitions.KEY_BUG_ID],
        )

        """
            create a symbolic link in the container:
                /experiment/{benchmark}/{bug_subject}/{bug_id}/{bug_subject}_{bug_id} ->
                                                                    /experiment/{benchmark}/{bug_subject}/{bug_id}/src/
        """
        bug_data_path_real = join(self.dir_expr, "src", "")
        bug_data_path_symlink = join(self.dir_expr, bug_id_str)
        symlink_command = "ln -s {0} {1}".format(
            bug_data_path_real, bug_data_path_symlink
        )
        self.run_command(symlink_command)
        fl_data = join(
            self.tbar_root_dir, "SuspiciousCodePositions", bug_id_str, "Ochiai.txt"
        )

        if not self.is_file(fl_data):
            utilities.error_exit(
                "There is no fault localization data. This is currently unsupported"
            )
            # emitter.debug("Making 'weak' fault Localization")
            # self.run_command(
            #     "mkdir -p {}".format(
            #         join(self.tbar_root_dir, "SuspiciousCodePositions", bug_id_str)
            #     )
            # )
            # f = self.read_file(
            #     join(
            #         self.dir_expr,
            #         "src",
            #         experiment_info[definitions.KEY_SOURCE_DIRECTORY],
            #         experiment_info["source_file"].replace(".", "/") + ".java",
            #     )
            # )
            # faulty_lines = [
            #     "{}@{}\n".format(experiment_info["source_file"], l)
            #     for l in range(len(f))
            # ]

            # self.write_file(faulty_lines, fl_data)

        return " ".join(
            [
                self.dir_expr,
                bug_id_str,
                defects4j_home,
                join(self.tbar_root_dir, "SuspiciousCodePositions"),
                self.dir_output + "/",
            ]
        )

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        tbar_logs_dir = join(self.tbar_root_dir, "logs")
        self.run_command("cp -r {0} {1}".format(tbar_logs_dir, self.dir_logs))

        # tbar_patches_dir = join(self.tbar_root_dir, "OUTPUT")
        # self.run_command("cp -r {0} {1}".format(tbar_patches_dir, self.dir_output))

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
        count_generated = 0
        count_plausible = 0
        count_enumerations = 0
        count_non_compilable = 0

        # count number of patch files
        # available only for FixPatterns
        list_patches_files_set = set()
        dir_output_fix_patterns = join(
            self.tbar_root_dir, "OUTPUT", "FixPatterns", "TBar"
        )
        list_output_fix_pattern_tbar_dir = self.list_dir(dir_output_fix_patterns)
        for dir_name in list_output_fix_pattern_tbar_dir:
            dir_fixed_bugs = join(dir_name, "FixedBugs")
            dir_fixed_bugs_ids_str = self.list_dir(dir_fixed_bugs)
            for dir_bug_id_str_name in dir_fixed_bugs_ids_str:
                list_patches_files = self.list_dir(dir_bug_id_str_name)
                for file_patch_path in list_patches_files:
                    file_patch_name = basename(file_patch_path)
                    if (
                        "Patch" in file_patch_name
                        and file_patch_name not in list_patches_files_set
                    ):
                        self._space.generated += 1
                        count_generated += 1
        self._space.generated = count_generated

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t[warning] no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")

            for line in log_lines:
                if "Patch Candidate" in line:
                    count_enumerations += 1
                if "failed compiling" in line:
                    count_non_compilable += 1
                if "Succeeded to fix the bug" in line:
                    count_plausible += 1
                    count_enumerations += 1
                elif (
                    "Partial succeeded to fix bug" in line
                    or "Failed to fix bug" in line
                ):
                    count_non_compilable += 1
                    count_enumerations += 1

        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        self._space.non_compilable = count_non_compilable
        self._error.is_error = is_error

        return self._space, self._time, self._error
