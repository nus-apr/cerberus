import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class APRER(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(APRER, self).__init__(self.name)
        self.image_name = "yeyehe/aprer:latest"
        self.hash_digest = (
            "7d5a41b7a9eb8ec744551752e57bc210b6bd39149990a15e0fb77e95526c100f"
        )

    def run_repair(self, bug_info, repair_config_info):
        super(APRER, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """
        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])
        passing_test_list = join(self.dir_expr, "src", bug_info["key_passing_tests"])
        failing_test_list = join(self.dir_expr, "src", bug_info["key_failing_tests"])
        patch_directory = join(self.dir_output, "patches")

        # execute repair tool
        # example : python3 start.py apache-commons-lang/bug-1/src/src/main/java apache-commons-lang/bug-1/src/src/test  apache-commons-lang/bug-1/src/target/classes apache-commons-lang/bug-1/src/target/test-classes org.apache.commons.lang3.RandomStringUtilsTest org.apache.commons.lang3.ValidateTest ./output
        command = (
            f"python3 start.py "
            f"--dir_java_src {dir_java_src} "
            f"--dir_test_src {dir_test_src} "
            f"--dir_java_bin {dir_java_bin} "
            f"--dir_test_bin {dir_test_bin} "
            f"--passing_test_list {passing_test_list} "
            f"--failing_test_list {failing_test_list} "
            f"--patch_directory {patch_directory}"
        )
        self.timestamp_log_start()
        status = self.run_command(command, log_file_path=self.log_output_path)
        self.process_status(status)
        self.timestamp_log_end()
