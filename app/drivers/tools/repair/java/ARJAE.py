import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class ARJAE(AbstractRepairTool):

    arjae_home = "/opt/arja"

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(ARJAE, self).__init__(self.name)
        self.image_name = "rshariffdeen/arjae"

    def run_repair(self, bug_info, config_info):
        super(ARJAE, self).run_repair(bug_info, config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])

        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])
        list_deps = [join(self.dir_expr, dep) for dep in bug_info["dependencies"]]
        list_deps.append(
            join(self.arjae_home, "external", "lib", "hamcrest-core-1.3.jar")
        )
        list_deps.append(join(self.arjae_home, "external", "lib", "junit-4.12.jar"))
        list_deps_str = ":".join(list_deps)

        max_generations = 2000000
        test_timeout = 30000
        # generate patches
        self.timestamp_log_start()
        arjae_command = (
            f"timeout -k 5m {timeout_h}h java -cp lib/*:bin us.msu.cse.repair.Main ArjaE "
            f"-DsrcJavaDir {dir_java_src} "
            f"-DbinJavaDir {dir_java_bin} "
            f"-DbinTestDir {dir_test_bin} "
            "-DdiffFormat true "
            f"-DexternalProjRoot {self.arjae_home}/external "
            f"-DwaitTime {test_timeout} "
            f"-DmaxGenerations {max_generations} "
            f"-DpatchOutputRoot {self.dir_output}/patches "
            f"-Ddependences {list_deps_str}"
        )

        status = self.run_command(arjae_command, self.log_output_path, self.arjae_home)

        if status != 0:
            self._error.is_error = True
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))

        self.timestamp_log_end()
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super(ARJAE, self).save_artifacts(dir_info)

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
                if "One fitness evaluation is finished" in line:
                    count_enumerations += 1
                elif "failed tests: 0" in line:
                    count_plausible += 1

        self._space.generated = len(
            [
                x
                for x in self.list_dir(
                    join(
                        self.dir_output,
                        "patch-valid" if values.use_valkyrie else "patches",
                    )
                )
                if ".txt" in x
            ]
        )
        self._space.enumerations = count_enumerations
        self._space.plausible = count_plausible

        return self._space, self._time, self._error
