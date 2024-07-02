import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.AnalysisToolStats import AnalysisToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool


class SanitizeParser(AbstractAnalyzeTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bindings = {
            join(values.dir_main, "sanitize_parser"): {
                "bind": "/tool",
                "mode": "rw",
            }
        }
        super().__init__(self.name)
        # preferably change to a container with the dependencies to reduce setup time
        self.image_name = "rshariffdeen/sanitizer-parser"

    def locate(self) -> None:
        pass

    def prepare_scripts(self, bug_info: Dict[str, Any]) -> str:
        self.emit_normal("generating wrapper scripts")
        self.run_command(f"mkdir -p {join(self.dir_setup, self.name)}")
        _test_path = join(self.dir_setup, self.name, "test.sh")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {self.dir_setup}\n",
                f"bash test.sh $(basename $1)\n",
            ],
            _test_path,
        )

        permission_cmd = f"chmod +x {_test_path}"
        self.run_command(permission_cmd)
        return _test_path

    def rerun_configuration(self, config_script: str, build_script: str) -> None:
        self.emit_normal("re-running configuration and build")
        _config_path = self.dir_expr + f"/{self.name}-config-build"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f"{config_script} {self.dir_expr}\n",
                f"{build_script} {self.dir_expr}\n",
            ],
            _config_path,
        )
        reconfig_command = "bash {}".format(_config_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-re-config-build.log")
        self.run_command(reconfig_command, log_file_path=log_reconfig_path)

    def instrument(self, bug_info: Dict[str, Any]) -> None:
        benchmark_name = bug_info[self.key_benchmark]
        config_script = bug_info.get(self.key_config_script, None)
        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        build_script = bug_info.get(self.key_build_script, None)
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")

        config_script = join(self.dir_setup, config_script)
        build_script = join(self.dir_setup, build_script)
        if str(benchmark_name).lower() == "vulnloc":
            self.test_script = self.prepare_scripts(bug_info)
            # rerun configration
            self.clean_subject(bug_info)
            self.rerun_configuration(config_script, build_script)

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
        timeout_m = str(float(timeout_h) * 60)

        tool_folder = (
            join(values.dir_main, "sanitize_parser")
            if self.locally_running
            else "/opt/sanitizer-parser/"
        )

        bug_info["cp_path"] = join(self.dir_setup)
        bug_info["cp_src"] = join(self.dir_expr, "src")
        bug_info["build_script"] = join(self.dir_setup, bug_info["build_script"])

        test_script = join(self.dir_setup, bug_info["test_script"])
        benchmark_name = bug_info[self.key_benchmark]
        if str(benchmark_name).lower() == "vulnloc":
            test_script = self.test_script
        bug_info["test_script"] = test_script

        metadata_path = join(self.dir_base_expr, "meta-data.json")
        self.write_json(bug_info, metadata_path)

        # generate patches
        self.timestamp_log_start()

        script_path = join(tool_folder, "san-trimmer.py")
        self.report_path = join(self.dir_output, "report.txt")
        status = self.run_command(
            f"python3 {script_path} {metadata_path} {self.dir_output}",
            self.log_output_path,
        )

        self.process_status(status)

        self.write_json(
            {"bug_reports": [join("reports", "report.txt")]},
            join(self.dir_output, "meta-data.json"),
        )

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        if self.is_file(self.report_path):
            self.run_command(f"mkdir -p {join(self.dir_setup, 'reports')}")
            copy_cmd = f"cp {self.report_path} {join(self.dir_setup, 'reports')}"
            self.run_command(copy_cmd)
        super(SanitizeParser, self).save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> AnalysisToolStats:
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
        self.stats.report_stats.generated = 0
        if self.is_file(self.report_path):
            content = self.read_file(self.report_path)
            if len(content) > 0:
                self.stats.report_stats.generated = 1

        return self.stats
