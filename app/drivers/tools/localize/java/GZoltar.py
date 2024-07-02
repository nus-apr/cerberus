import os
import re
from os.path import dirname
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class GZoltar(AbstractLocalizeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/gzoltar:latest"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        self.output_file = ""
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]

        gzoltar_version = "1.7.4-SNAPSHOT"

        env = {}
        if bug_info.get(self.key_language, "") == "java":
            env["JAVA_HOME"] = "/usr/lib/jvm/java-{}-openjdk-amd64".format(
                bug_info.get("java_version", 8)
            )
            if int(bug_info.get("java_version", 8)) == 8:
                self.run_command(
                    f"update-java-alternatives -s java-1.8.0-openjdk-amd64"
                )

        self.emit_normal("Building project")
        if self.key_build_script in bug_info:
            build_script = bug_info[self.key_build_script]
            self.run_command(
                "bash " + build_script, self.log_output_path, self.dir_setup, env=env
            )
        else:
            self.run_command(
                "mvn clean compile test-compile",
                self.log_output_path,
                join(self.dir_expr, "src"),
                env=env,
            )

        if bug_info.get("build_system", "NAN") == "maven":
            self.run_command(
                "mvn dependency:copy-dependencies",
                self.log_output_path,
                join(self.dir_expr, "src"),
                env=env,
            )

        tests_list = join(self.dir_expr, "unit-tests.txt")

        deps_location_test = join(
            self.dir_expr, "src", dirname(bug_info[self.key_dir_class]), "dependency"
        )
        if self.is_dir(deps_location_test):
            deps_location = ":" + join(deps_location_test, "*")
        else:
            deps_location = ""

        self.timestamp_log_start()
        self.emit_normal("Generating test method list")
        self.run_command(
            "java -cp {test_dir}:{junit}:{hamcrest}:{gzoltar_cli}{deps} com.gzoltar.cli.Main listTestMethods {test_dir} --outputFile {output}".format(
                output=tests_list,
                hamcrest="/gzoltar/libs/hamcrest-core.jar",
                deps=deps_location,
                junit="/gzoltar/libs/junit.jar",
                test_dir=join(self.dir_expr, "src", bug_info[self.key_dir_test_class]),
                gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                    gzoltar_version
                ),
            ),
            log_file_path=self.log_output_path,
            dir_path=join(self.dir_expr, "src"),
            env=env,
        )

        if not self.is_file(tests_list):
            self.error_exit("No test list generated")

        self.emit_normal("Instrumenting project")

        self.run_command(
            "mv {class_dir} {backup_dir}".format(
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
                backup_dir=join(self.dir_expr, "src", "class-backup"),
            )
        )

        self.run_command(
            "java -cp {backup_dir}:{gzoltar_agent}:{gzoltar_cli}{deps} com.gzoltar.cli.Main instrument --outputDirectory {class_dir} {backup_dir}".format(
                backup_dir=join(self.dir_expr, "src", "class-backup"),
                deps=deps_location,
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
                gzoltar_agent="/gzoltar/com.gzoltar.agent.rt/target/com.gzoltar.agent.rt-{}-all.jar".format(
                    gzoltar_version
                ),
                gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                    gzoltar_version
                ),
            ),
            log_file_path=self.log_output_path,
            env=env,
        )

        self.emit_normal("Running each unit test case in isolation")

        ser_file = join(self.dir_output, "ser_file.ser")
        self.run_command(
            """java -cp {test_dir}:{class_dir}:{junit}:{hamcrest}:{gzoltar_agent}:{gzoltar_cli}{deps} -Dgzoltar-agent.destfile={ser_file} -Dgzoltar-agent.output="file" \
                            com.gzoltar.cli.Main runTestMethods --testMethods {test_method} --offline --collectCoverage""".format(
                test_dir=join(self.dir_expr, "src", bug_info[self.key_dir_test_class]),
                deps=deps_location,
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
                junit="/gzoltar/libs/junit.jar",
                hamcrest="/gzoltar/libs/hamcrest-core.jar",
                gzoltar_agent="/gzoltar/com.gzoltar.agent.rt/target/com.gzoltar.agent.rt-{}-all.jar".format(
                    gzoltar_version
                ),
                gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                    gzoltar_version
                ),
                test_method=tests_list,
                ser_file=ser_file,
            ),
            log_file_path=self.log_output_path,
            env=env,
        )

        self.emit_normal("Restore classes")
        self.run_command(
            "rm -rf {class_dir}".format(
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class])
            )
        )
        self.run_command(
            "mv {backup_dir} {class_dir}".format(
                backup_dir=join(self.dir_expr, "src", "class-backup"),
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
            )
        )

        self.emit_normal("Generate report")

        formula = bug_info.get("fl_formula", "Ochiai").lower()
        metric = bug_info.get("fl_metric", "entropy").lower()
        granularity = bug_info.get("fl_granularity", "line").lower()
        localize_command = """ java -cp {class_dir}:{test_dir}:{junit}:{hamcrest}:{gzoltar_cli}{deps} \
  com.gzoltar.cli.Main faultLocalizationReport \
    --buildLocation "{class_dir}" \
    --granularity "{granularity}" \
    --inclPublicMethods \
    --inclStaticConstructors \
    --inclDeprecatedMethods \
    --dataFile "{ser_file}" \
    --outputDirectory "{output_dir}" \
    --family "sfl" \
    --formula "{formula}" \
    --metric "{metric}" \
    --formatter "txt" {additional_params} """.format(
            formula=formula,
            metric=metric,
            deps=deps_location,
            granularity=granularity,
            class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
            output_dir=join(self.dir_output),
            additional_params=additional_tool_param,
            ser_file=ser_file,
            test_dir=join(self.dir_expr, "src", bug_info[self.key_dir_test_class]),
            junit="/gzoltar/libs/junit.jar",
            hamcrest="/gzoltar/libs/hamcrest-core.jar",
            gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                gzoltar_version
            ),
        )

        status = self.run_command(
            localize_command,
            self.log_output_path,
            dir_path=join(self.dir_expr, "src"),
            env=env,
        )
        self.process_status(status)

        self.output_file = join(self.dir_output, "sfl", "txt", "ochiai.ranking.csv")

        if self.is_file(self.output_file):
            localization = []
            lines = self.read_file(self.output_file)[1:]
            for entry in lines:
                entry = entry.strip()
                path_line, score = entry.split(";")
                reference, line = path_line.split(":")
                second_dollar = None
                try:
                    first_dollar = reference.index("$")
                    second_dollar = first_dollar + reference[first_dollar + 1 :].index(
                        "$"
                    )
                except Exception as e:
                    pass
                path = (
                    "src/main/java/"
                    + reference.split("#")[0]
                    .replace(".", "/")[
                        : second_dollar + 1 if second_dollar is not None else None
                    ]
                    .replace("$", "/")
                    + ".java"
                )
                localization.append(
                    {
                        "source_file": path,
                        "function": reference,
                        "line_numbers": [line],
                        "score": score,
                    }
                )
            passing_identifiers = []
            failing_identifiers = []
            for test_line in self.read_file(
                join(self.dir_output, "sfl", "txt", "tests.csv")
            )[1:]:
                test_line = test_line.strip()
                identifier, outcome, runtime, stack_trace, *rest = test_line.split(",")
                if outcome == "PASS":
                    passing_identifiers.append(identifier)
                elif outcome == "FAIL":
                    failing_identifiers.append(identifier)
                else:
                    self.emit_warning("INVALID OUTCOME?? {}".format(outcome))

            new_metadata = {
                self.key_passing_test_identifiers: passing_identifiers,
                self.key_failing_test_identifiers: failing_identifiers,
                self.key_analysis_output: [
                    {
                        "generator": "gzoltar",
                        "confidence": 1,
                        "localization": localization[:10],
                    }
                ],
            }
            self.write_json([new_metadata], join(self.dir_output, "meta-data.json"))

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> LocalizeToolStats:
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False
        if self.output_file and self.is_file(self.output_file):
            output_lines = self.read_file(self.output_file, encoding="iso-8859-1")
            self.stats.fix_loc_stats.fix_locs = len(output_lines) - 1
        else:
            self.emit_error("no output file found")
            self.stats.error_stats.is_error = True

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
