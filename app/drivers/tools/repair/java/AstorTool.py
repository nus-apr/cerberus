import math
import re
from os.path import join
from typing import Optional

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class AstorTool(AbstractRepairTool):

    astor_home = "/opt/astor"
    astor_version = "2.0.0"
    mode: Optional[str] = None

    def __init__(self):
        super().__init__(self.name)
        self.image_name = "rshariffdeen/astor"

    def run_repair(self, bug_info, repair_config_info):
        super(AstorTool, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(repair_config_info[self.key_timeout])
        timeout_m = str(float(timeout_h) * 60)
        max_gen = 1000000

        dir_java_src = join(self.dir_expr, "src", bug_info[self.key_dir_source])
        dir_test_src = join(self.dir_expr, "src", bug_info[self.key_dir_tests])
        dir_java_bin = bug_info[self.key_dir_source]
        dir_test_bin = bug_info[self.key_dir_test_class]

        # there is a bug in running Lang subjects with asm.jar
        list_deps = [
            f"{self.dir_expr}/{x}"
            for x in bug_info["dependencies"]
            if not (bug_info[self.key_subject].lower() == "lang" and "asm.jar" in x)
        ]
        list_deps.append(f"{self.astor_home}/external/lib/hamcrest-core-1.3.jar")
        list_deps.append(f"{self.astor_home}/external/lib/junit-4.11.jar")
        list_deps_str = ":".join(list_deps)

        # generate patches
        self.timestamp_log_start()
        repair_command = (
            f"timeout -k 5m {timeout_h}h "
            f"java -cp target/astor-{self.astor_version}-jar-with-dependencies.jar "
            f"fr.inria.main.evolution.AstorMain "
            f"-mode {self.mode} "
            + (f"-loglevel DEBUG " if self.is_debug else "-loglevel INFO ")
            + f"-srcjavafolder {dir_java_src} "
            f"-srctestfolder {dir_test_src}  "
            f"-binjavafolder {dir_java_bin} "
            f"-bintestfolder  {dir_test_bin} "
            f"-location {self.dir_expr}/src "
            f"-dependencies {list_deps_str} "
            f"-maxgen {max_gen} "
            f"-maxtime {int(math.ceil(float(timeout_m)))} "
            f"-stopfirst false "
        )

        status = self.run_command(repair_command, self.log_output_path, self.astor_home)

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
        list_artifact_dirs = [
            self.astor_home + "/" + x for x in ["diffSolutions", "output_astor"]
        ]
        for d in list_artifact_dirs:
            copy_command = f"cp -rf {d} {self.dir_output}"
            self.run_command(copy_command)
        super(AstorTool, self).save_artifacts(dir_info)

    def analyse_output(self, dir_info, bug_id, fail_list):
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
        count_compilable = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
            self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "child compiles" in line.lower():
                    count_compilable += 1
                    identifier = re.search(r"id (.*)", line)
                    if not identifier:
                        self.emit_warning("No Id found")
                        continue
                    child_id = int(str(identifier.group(1)).strip())
                    if child_id > count_enumerations:
                        count_enumerations = child_id
                elif "found solution," in line.lower():
                    count_plausible += 1

        self.stats.patch_stats.generated = len(
            [
                x
                for x in self.list_dir(join(self.astor_home, "diffSolutions"))
                if ".diff" in x
            ]
        )
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.non_compilable = count_enumerations - count_compilable

        return self.stats
