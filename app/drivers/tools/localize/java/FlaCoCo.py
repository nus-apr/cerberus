import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.LocalizeToolStats import LocalizeToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool


class FlaCoCo(AbstractLocalizeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/flacoco:latest"

    def generate_meta_data(self, localization_file_path: str) -> None:
        localization = []
        lines = self.read_file(localization_file_path)
        for entry in lines:
            path, line, score = entry.split(",")
            localization.append(
                {
                    "source_file": path,
                    "line_numbers": [line],
                    "score": score,
                }
            )
        new_metadata = {
            self.key_analysis_output: [
                {
                    "generator": self.name,
                    "confidence": 1,
                    "localization": localization,
                }
            ]
        }
        self.write_json([new_metadata], join(self.dir_output, "meta-data.json"))

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]

        formula = bug_info.get(self.key_fl_formula, "Ochiai").upper()

        env = {}
        if bug_info.get(self.key_language, "") == "java":
            env["JAVA_HOME"] = "/usr/lib/jvm/java-{}-openjdk-amd64".format(
                bug_info.get("java_version", 8)
            )
            if int(bug_info.get("java_version", 8)) == 8:
                self.run_command(
                    f"update-java-alternatives -s java-1.8.0-openjdk-amd64"
                )

        if self.key_clean_script in bug_info:
            self.run_command(
                "bash {}".format(bug_info[self.key_clean_script]),
                dir_path=self.dir_setup,
                env=env,
            )
        else:
            if bug_info["build_system"] == "maven":
                self.run_command(
                    "mvn clean", dir_path=join(self.dir_expr, "src"), env=env
                )
            else:
                pass

        if self.key_build_script in bug_info:
            self.run_command(
                "bash {}".format(bug_info[self.key_build_script]),
                dir_path=self.dir_setup,
                env=env,
            )
        else:
            if bug_info["build_system"] == "maven":
                self.run_command(
                    "mvn compile test-compile",
                    dir_path=join(self.dir_expr, "src"),
                    env=env,
                )
            else:
                pass

        self.timestamp_log_start()
        localization_file_path = join(self.dir_output, "localization.csv")
        localize_command = "timeout -k 5m {}h java -jar /flacoco/target/flacoco-1.0.7-SNAPSHOT-jar-with-dependencies.jar -f {} --projectpath {} {} -o {} {}".format(
            timeout,
            formula,
            join(self.dir_expr, "src"),
            additional_tool_param,
            localization_file_path,
            "-v" if values.debug else "",
        )

        status = self.run_command(localize_command, self.log_output_path, env=env)
        self.process_status(status)

        if self.is_file(localization_file_path):
            self.generate_meta_data(localization_file_path)
        else:
            localization = []
            new_metadata = {
                self.key_analysis_output: [
                    {
                        "generator": self.name,
                        "confidence": 1,
                        "localization": localization,
                    }
                ]
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

        output_file = join(self.dir_output, "localization.csv")
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
            unique_class_list = set()
            for result in output_lines:
                class_name, line_number, score = result.split(",")
                unique_class_list.add(class_name)
            self.stats.fix_loc_stats.source_files = len(unique_class_list)
            self.stats.fix_loc_stats.fix_locs = len(output_lines)
        else:
            self.emit_error("no localization file found")
            self.stats.error_stats.is_error = True

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
