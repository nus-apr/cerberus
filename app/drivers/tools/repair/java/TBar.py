import os
import re
from os.path import basename
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Set

from app.core import definitions
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class TBar(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.tbar_root_dir = "/TBar"
        self.image_name = "mirchevmp/tbar-cerberus:latest"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        """
        self.dir_logs - directory to store logs
        self.dir_setup - directory to access setup scripts
        self.dir_expr - directory for experiment
        self.dir_output - directory to store artifacts/output
        """
        if self.is_instrument_only:
            return

        dir_tbar_exist = self.is_dir(self.tbar_root_dir)
        if not dir_tbar_exist:
            # self.emit_error(
            #     "[Exception] TBar repo is not at the expected location. "
            #     "Please double check whether we are in TBar container."
            # )
            self.error_exit("TBar repo is not at the expected location.")
        timeout_h = str(task_config_info[self.key_timeout])
        additional_tool_param = task_config_info[self.key_tool_params]

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

        if bug_info.get(self.key_java_version) == 7:
            bug_info[self.key_java_version] = 8

        env = dict(
            FAILING_TESTS=(" ".join(bug_info[self.key_failing_test_identifiers])),
            PASSING_TESTS=(" ".join(bug_info[self.key_passing_test_identifiers])),
            CLASS_DIRECTORY=f"{bug_info[self.key_dir_class]}/",
            TEST_CLASS_DIRECTORY=f"{bug_info[self.key_dir_test_class]}/",
            SOURCE_DIRECTORY=f"{bug_info[self.key_dir_source]}/",
            TEST_SOURCE_DIRECTORY=f"{bug_info[self.key_dir_tests]}/",
            JAVA_HOME=f"/usr/lib/jvm/java-{bug_info.get(self.key_java_version,8)}-openjdk-amd64/",
        )
        if self.key_build_script in bug_info:
            env["BUILD_SCRIPT"] = join(self.dir_setup, bug_info[self.key_build_script])

        # start running
        self.timestamp_log_start()

        run_fl = task_config_info[definitions.KEY_CONFIG_FIX_LOC] == "tool"
        parameters = self.create_parameters(bug_info, run_fl, env)

        tbar_command = (
            f"timeout -k 10s {timeout_h}h java -cp 'target/classes:target/dependency/*'"
            f" edu.lu.uni.serval.tbar.main.Main {parameters} {additional_tool_param}"
        )

        status = self.run_command(
            tbar_command,
            log_file_path=self.log_output_path,
            dir_path=self.tbar_root_dir,
            env=env,
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def create_parameters(
        self, bug_info: Dict[str, Any], run_fl: bool, env: Dict[str, str]
    ) -> str:
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
            bug_info[self.key_subject],
            bug_info[self.key_bug_id],
        )

        """
            create a symbolic link in the container:
                /experiment/{benchmark}/{bug_subject}/{bug_id}/{bug_subject}_{bug_id} ->
                                                                    /experiment/{benchmark}/{bug_subject}/{bug_id}/src/
        """
        bug_data_path_real = join(self.dir_expr, "src", "")
        bug_data_path_symlink = join(self.dir_expr, bug_id_str)
        dir_java_bin = join(self.dir_expr, "src", bug_info[self.key_dir_class])
        dir_test_bin = join(self.dir_expr, "src", bug_info[self.key_dir_test_class])
        list_deps = [
            join(self.dir_expr, dep) for dep in bug_info[self.key_dependencies]
        ]
        list_deps_str = ":".join(list_deps)
        symlink_command = "ln -s {0} {1}".format(
            bug_data_path_real, bug_data_path_symlink
        )

        self.run_command(symlink_command)

        failed_tests_dir = join(self.tbar_root_dir, "FailedTestCases/")
        self.run_command(f"mkdir -p {failed_tests_dir}")
        failed_tests_file = join(
            failed_tests_dir,
            f"{bug_info[self.key_bug_id].replace('-', '_')}.txt",
        )
        self.run_command("mkdir -p {}".format(os.path.dirname(failed_tests_file)))

        self.emit_debug("I am looking for {}".format(failed_tests_file))
        fl_out_dir = join(self.tbar_root_dir, "SuspiciousCodePositions/")
        self.run_command(f"mkdir -p {fl_out_dir}")
        fl_data = join(fl_out_dir, bug_id_str, "Ochiai.txt")
        # Temporary solution: copying to new path
        fl_folder = f"{bug_info[self.key_bug_id].replace('-', '_')}"
        orig_path = join(
            fl_out_dir, fl_folder, "Ochiai.txt"
        )  # /TBar/SuspiciousCodePositions/{subject}_id
        new_path = join(
            fl_out_dir, bug_id_str
        )  # /TBar/SuspiciousCodePositions/{subject}_{bug_id_str}
        self.run_command("mkdir -p {}".format(os.path.dirname(fl_data)))
        self.run_command(f"cp {orig_path} {new_path}")

        failed_tests_file_copy = join(
            self.tbar_root_dir,
            "FailedTestCases/",
            f"{bug_id_str}.txt",
        )
        # Specifying failing module
        failing_module = bug_info.get("failing_module", "")
        
        # Run build script
        self.run_command(
                f"bash {join(self.dir_setup,bug_info[self.key_build_script])}"
            )
        
        if not run_fl:
            self.emit_debug("Creating FL data file from provided info")
            self.write_fl_data(bug_info, failed_tests_file, fl_data)
        else:
            cmd = f"bash ./FL.sh {join(self.dir_expr,'src', failing_module)} {bug_id_str} {dir_java_bin} {dir_test_bin} {list_deps_str}"
            self.run_command(
                cmd,
                dir_path=self.tbar_root_dir,
                env=env,
                log_file_path=self.log_output_path,
            )
        # actually, this is needed only for non-maven projects, but do it anyway
        self.run_command(f"ln -sf {failed_tests_file} {failed_tests_file_copy}")

        if not self.is_file(fl_data):
            if run_fl:
                msg = f"Fault localization did not generate expected file: {fl_data}"
            else:
                msg = f"Fault localization not provided; expected {fl_data}"
            self.error_exit(msg)

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

    def write_fl_data(
        self, bug_info: Dict[str, Any], failed_tests_file: str, fl_data: str
    ) -> None:
        self.run_command(f"rm -f {failed_tests_file}")
        self.run_command(f"rm -f {fl_data}")

        failing_tests = bug_info[self.key_failing_test_identifiers]
        lines = [f"Failing tests: {len(failing_tests)}:\n"]
        lines.extend(f"  - {name.replace('#', '::')}\n" for name in failing_tests)
        self.write_file(lines, failed_tests_file)

        test_failed_tests_file = self.is_file(failed_tests_file)

        self.emit_debug("Bug info is {}".format(bug_info))
        self.emit_debug("Localization is {}".format(bug_info[self.key_localization]))
        lines = []
        for x in bug_info[self.key_localization]:
            classname = x["function"].split("#")[0].replace("$", ".", 1)
            classname = re.sub(r"\$\d+$", "", classname)
            lines.extend(f"{classname}@{lineno}\n" for lineno in x["line_numbers"])
        self.emit_debug("Writing [{}] to {}".format(lines, fl_data))
        self.write_file(lines, fl_data)

        test_fl_data = self.is_file(fl_data)
        if not test_fl_data:
            self.error_exit("Suspiciousness file was not written. Unsupported state")
        self.emit_debug(f"{test_failed_tests_file} {test_fl_data}")

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """

        tbar_logs_dir = join(self.tbar_root_dir, "logs")
        self.run_command("cp -r {0} {1}".format(tbar_logs_dir, self.dir_logs))

        self.run_command(f"mkdir -p {self.dir_patch}")
        self.run_command(
            "bash -c 'cp -r $(find {}/TBar | grep .txt) {}'".format(
                self.dir_output, self.dir_patch
            ),
            dir_path=self.dir_output,
        )

        # tbar_patches_dir = join(self.tbar_root_dir, "OUTPUT")
        # self.run_command("cp -r {0} {1}".format(tbar_patches_dir, self.dir_output))

        super().save_artifacts(dir_info)
        return

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

        is_error = False
        count_generated = 0
        count_plausible = 0
        count_enumerations = 0
        count_non_compilable = 0

        # count number of patch files
        # available only for FixPatterns
        list_patches_files_set: Set[str] = set()
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
                        self.stats.patch_stats.generated += 1
                        count_generated += 1
        self.stats.patch_stats.generated = count_generated

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")

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

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.non_compilable = count_non_compilable
        self.stats.error_stats.is_error = is_error

        return self.stats
    