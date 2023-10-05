import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class ARJA(AbstractRepairTool):

    arja_home = "/opt/arja"

    d4j_env = {"TZ": "America/Los_Angeles"}

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/arja"

    def run_repair(self, bug_info, repair_config_info):
        super(ARJA, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(repair_config_info[self.key_timeout])

        classpath = f"{join(self.arja_home,'lib/*')}:{join(self.arja_home,'bin')}"

        passing_test_list = bug_info[self.key_passing_tests]
        failing_test_list = bug_info[self.key_failing_tests]

        dir_java_src = join(self.dir_expr, "src", bug_info[self.key_dir_source])
        dir_test_src = join(self.dir_expr, "src", bug_info[self.key_dir_tests])
        dir_java_bin = join(self.dir_expr, "src", bug_info[self.key_dir_class])
        dir_test_bin = join(self.dir_expr, "src", bug_info[self.key_dir_test_class])
        list_deps = [
            join(self.dir_expr, dep) for dep in bug_info[self.key_dependencies]
        ]
        list_deps.append(
            join(self.arja_home, "external", "lib", "hamcrest-core-1.3.jar")
        )
        list_deps.append(join(self.arja_home, "external", "lib", "junit-4.11.jar"))
        list_deps_str = ":".join(list_deps)

        arja_default_population_size = 40
        # use a large one to keep ARJA running forever
        # there is `populationSize * maxGenerations` as an `int` in ARJA; do not overflow
        max_generations = 0x7FFFFFFF // (arja_default_population_size + 1)

        test_timeout = 30000
        # generate patches
        self.timestamp_log_start()
        arja_command = (
            f"timeout -k 5m {timeout_h}h java -cp {classpath} us.msu.cse.repair.Main Arja "
            f"-DsrcJavaDir {dir_java_src} "
            f"-DbinJavaDir {dir_java_bin} "
            f"-DbinTestDir {dir_test_bin} "
            "-DdiffFormat true "
            f"-DexternalProjRoot {self.arja_home}/external "
            f"-DwaitTime {test_timeout} "
            f"-DmaxGenerations {max_generations} "
            f"-DpatchOutputRoot {self.dir_output}/patches "
            f"-Ddependences {list_deps_str} "
            f"-DpopulationSize {arja_default_population_size}"
        )

        if not passing_test_list:
            test_list_str = ",".join(failing_test_list)
            arja_command += f" -Dtests {test_list_str}"

        status = self.run_command(
            arja_command,
            self.log_output_path,
            dir_path=join(self.dir_expr, "src"),
            env=self.d4j_env,
        )

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
        super(ARJA, self).save_artifacts(dir_info)

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
