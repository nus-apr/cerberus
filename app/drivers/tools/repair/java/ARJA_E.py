import datetime
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


class ARJA_E(AbstractRepairTool):
    arja_e_home = "/opt/arja"
    d4j_env = {"TZ": "America/Los_Angeles"}

    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "hzhenxin/arjae"

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

        classpath = f"{join(self.arja_e_home, 'lib/*')}:{join(self.arja_e_home, 'bin')}:/root/.m2/repository/*"

        dir_java_src = join(self.dir_expr, "src", bug_info[self.key_dir_source])
        dir_test_src = join(self.dir_expr, "src", bug_info[self.key_dir_tests])
        dir_java_bin = join(self.dir_expr, "src", bug_info[self.key_dir_class])
        dir_test_bin = join(self.dir_expr, "src", bug_info[self.key_dir_test_class])
        passing_test_identifiers_list = bug_info[self.key_passing_test_identifiers]
        failing_test_identifiers_list = bug_info[self.key_failing_test_identifiers]

        env = self.d4j_env.copy()
        java_version = bug_info.get(self.key_java_version, 8)
        if int(java_version) <= 7:
            java_version = 8
        env["JAVA_HOME"] = f"/usr/lib/jvm/java-{java_version}-openjdk-amd64/"

        self.run_command(
            "bash {}".format(bug_info.get(self.key_build_script)),
            dir_path=self.dir_setup,
            env=env,
        )

        list_deps = [
            join(self.dir_expr, dep) for dep in bug_info[self.key_dependencies]
        ]
        list_deps += [
            join(self.arja_e_home, "external", "lib", "hamcrest-core-1.3.jar"),
            join(self.arja_e_home, "external", "lib", "junit-4.12.jar"),
        ]

        list_deps_str = ":".join(list_deps)
        dir_localization = f"{self.dir_output}/localization"
        if task_config_info[definitions.KEY_CONFIG_FIX_LOC] != "tool":
            self.run_command(f"mkdir {dir_localization}")
            localization_lines = self.transform_localization(
                bug_info[self.key_localization]
            )
            self.write_file(localization_lines, join(dir_localization, "spectra"))

            test_name_lines = (
                ["name,outcome,runtime,stacktrace\n"]
                + [
                    f"{name},FAIL,0,\n"
                    for name in bug_info[self.key_failing_test_identifiers]
                ]
                + [
                    f"{name},PASS,0,\n"
                    for name in bug_info[self.key_passing_test_identifiers]
                ]
            )
            self.write_file(test_name_lines, join(dir_localization, "tests"))

        arja_default_population_size = 40
        # use a large one to keep ARJA running forever
        # there is `populationSize * maxGenerations` as an `int` in ARJA; do not overflow
        max_generations = 0x7FFFFFFF // (arja_default_population_size + 1)

        test_timeout = 20
        java_version = bug_info[self.key_java_version]
        repair_timeout = int(datetime.timedelta(days=365).total_seconds() // 60)
        # generate patches
        self.timestamp_log_start()
        arja_e_command = (
            f"timeout -k 5m {timeout_h}h java -cp {classpath} us.msu.cse.repair.Main ArjaE "
            f"-DsrcJavaDir {dir_java_src} "
            f"-DbinJavaDir {dir_java_bin} "
            f"-DbinTestDir {dir_test_bin} "
            "-DdiffFormat true "
            f" -DsrcVersion={java_version} "
            f"-DexternalProjRoot {self.arja_e_home}/external "
            f"-DwaitTime {test_timeout} "
            f"-DmaxGenerations {max_generations} "
            f"-DpatchOutputRoot {self.dir_output}/patches "
            f"-Ddependences {list_deps_str} "
            f"-DmaxTime {repair_timeout} "
            f"-DpopulationSize {arja_default_population_size} "
            f"-DgzoltarDataDir {dir_localization} "
        )

        env = self.d4j_env.copy()
        java_version = bug_info.get(self.key_java_version, 8)
        if int(java_version) <= 7:
            java_version = 8
        env["JAVA_HOME"] = f"/usr/lib/jvm/java-{java_version}-openjdk-amd64/"

        self.run_command(
            "bash {}".format(bug_info.get(self.key_build_script)),
            dir_path=self.dir_setup,
            env=env,
        )

        if bug_info[self.key_build_system] == "maven":
            self.run_command(
                f"mvn dependency:copy-dependencies",
                dir_path=join(self.dir_expr, "src"),
                env=env,
            )

        if not passing_test_identifiers_list:
            test_list_str = ",".join(failing_test_identifiers_list)
            arja_e_command += f" -Dtests {test_list_str}"

        status = self.run_command(
            arja_e_command,
            self.log_output_path,
            dir_path=join(self.dir_expr, "src"),
            env=env,
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
        super(ARJA_E, self).save_artifacts(dir_info)

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

        count_plausible = 0
        count_enumerations = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("(warning) no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "One fitness evaluation is finished" in line:
                    count_enumerations += 1
                elif "failed tests: 0" in line:
                    count_plausible += 1

        self.stats.patch_stats.generated = len(
            [
                x
                for x in self.list_dir(
                    join(
                        self.dir_output,
                        "patch-valid" if self.use_valkyrie else "patches",
                    )
                )
                if ".txt" in x
            ]
        )
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible

        return self.stats

    def transform_localization(self, data: List[Dict[str, Any]]) -> List[str]:
        # Examples:
        # org.jsoup.parser$TokeniserState$37#read(org.jsoup.parser.Tokeniser,org.jsoup.parser.CharacterReader)
        # org.jsoup.parser$Parser#xmlParser()
        lines = ["name;suspiciousness_value\n"]
        for x in data:
            suspiciousness = x["score"]
            method = x["function"]
            classname = method.split("#")[0].replace("$", ".", 1)
            classname = re.sub(r"\$\d+$", "", classname)
            for lineno in x["line_numbers"]:
                lines.append(f"<{classname}{{#{lineno},{suspiciousness}\n")
        return lines
