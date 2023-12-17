import os
import re
from os.path import join

from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class GZoltar(AbstractLocalizeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/gzoltar:latest"
        self.id = ""

    def run_localization(self, bug_info, localization_config_info):
        super(GZoltar, self).run_localization(bug_info, localization_config_info)
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(localization_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = localization_config_info[self.key_tool_params]

        gzoltar_version = "1.7.4-SNAPSHOT"

        self.emit_normal("Building project")
        if self.key_build_script in bug_info:
            build_script = bug_info[self.key_build_script]
            self.run_command(
                "bash " + build_script, self.log_output_path, self.dir_setup
            )
        else:
            self.run_command(
                "mvn clean compile test-compile",
                self.log_output_path,
                join(self.dir_expr, "src"),
            )

        tests_list = join(self.dir_expr, "unit-tests.txt")

        self.timestamp_log_start()
        self.emit_normal("Generating test method list")
        self.run_command(
            "java -cp {test_dir}:{junit}:{hamcrest}:{gzoltar_cli} com.gzoltar.cli.Main listTestMethods {test_dir} --outputFile {output}".format(
                output=tests_list,
                hamcrest="/gzoltar/libs/hamcrest-core.jar",
                junit="/gzoltar/libs/junit.jar",
                test_dir=join(self.dir_expr, "src", bug_info[self.key_dir_test_class]),
                gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                    gzoltar_version
                ),
            ),
            dir_path=join(self.dir_expr, "src"),
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
            "java -cp {backup_dir}:{gzoltar_agent}:{gzoltar_cli} com.gzoltar.cli.Main instrument --outputDirectory {class_dir} {backup_dir}".format(
                backup_dir=join(self.dir_expr, "src", "class-backup"),
                class_dir=join(self.dir_expr, "src", bug_info[self.key_dir_class]),
                gzoltar_agent="/gzoltar/com.gzoltar.agent.rt/target/com.gzoltar.agent.rt-{}-all.jar".format(
                    gzoltar_version
                ),
                gzoltar_cli="/gzoltar/com.gzoltar.cli/target/com.gzoltar.cli-{}-jar-with-dependencies.jar".format(
                    gzoltar_version
                ),
            )
        )

        self.emit_normal("Running each unit test case in isolation")

        ser_file = join(self.dir_output, "ser_file.ser")
        self.run_command(
            """java -cp {test_dir}:{class_dir}:{junit}:{hamcrest}:{gzoltar_agent}:{gzoltar_cli} -Dgzoltar-agent.destfile={ser_file} -Dgzoltar-agent.output="file" \
                            com.gzoltar.cli.Main runTestMethods --testMethods {test_method} --offline --collectCoverage""".format(
                test_dir=join(self.dir_expr, "src", bug_info[self.key_dir_test_class]),
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
            )
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
        localize_command = """ java -cp {class_dir}:{test_dir}:{junit}:{hamcrest}:{gzoltar_cli} \
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
            localize_command, self.log_output_path, dir_path=join(self.dir_expr, "src")
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        output_file = join(self.dir_output, "localilzation.csv")
        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False
        if self.is_file(output_file):
            output_lines = self.read_file(output_file, encoding="iso-8859-1")
            self.stats.fix_loc_stats.plausible = len(output_lines)
            self.stats.fix_loc_stats.generated = len(output_lines)

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
