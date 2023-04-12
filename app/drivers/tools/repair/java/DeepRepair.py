import os
import re
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class DeepRepair(AbstractRepairTool):

    astor_home = "/opt/astor"
    astor_version = "2.0.0"

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(DeepRepair, self).__init__(self.name)
        self.image_name = "rshariffdeen/astor"

    def run_repair(self, bug_info, config_info):
        super(DeepRepair, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])

        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = bug_info["class_directory"]
        dir_test_bin = bug_info["test_class_directory"]
        list_deps = bug_info["dependencies"]
        list_deps.append(f"{self.astor_home}/external/lib/hamcrest-core-1.3.jar")
        list_deps.append(f"{self.astor_home}/external/lib/junit-4.11.jar")
        list_deps_str = ":".join(list_deps)

        # generate patches
        self.timestamp_log_start()
        repair_command = (
            f"timeout -v -k 5m {timeout_h}h "
            f"java -cp target/astor-{self.astor_version}-jar-with-dependencies.jar "
            f"fr.inria.main.evolution.AstorMain "
            f"-mode deeprepair "
            f"-srcjavafolder {dir_java_src} "
            f"-srctestfolder {dir_test_src}  "
            f"-binjavafolder {dir_java_bin} "
            f"-bintestfolder  {dir_test_bin} "
            f"-location {self.dir_expr}/src "
            f"-dependencies {list_deps_str}"
        )

        status = self.run_command(repair_command, self.log_output_path, self.astor_home)

        self.process_status(status)

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

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
        super(DeepRepair, self).save_artifacts(dir_info)

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
        count_compilable = 0

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self._space.generated = len(
            [name for name in list_output_dir if ".patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "child compiles" in line.lower():
                    count_compilable += 1
                    identifier = re.search(r"id (.*)", line)
                    if not identifier:
                        emitter.warning("Could not find id")
                        continue
                    child_id = int(str(identifier.group(1)).strip())
                    if child_id > count_enumerations:
                        count_enumerations = child_id
                elif "found solution," in line.lower():
                    count_plausible += 1

        self._space.generated = len(
            [
                x
                for x in self.list_dir(join(self.astor_home, "diffSolutions"))
                if ".diff" in x
            ]
        )
        self._space.enumerations = count_enumerations
        self._space.plausible = count_plausible
        self._space.non_compilable = count_enumerations - count_compilable

        return self._space, self._time, self._error
