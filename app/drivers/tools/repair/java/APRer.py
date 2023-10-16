import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class APRER(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(APRER, self).__init__(self.name)
        self.image_name = "yeyehe/aprer:latest"
        self.hash_digest = (
            "a6200d594b28b1b0d8aadebcd995f861abb94d7bd93445f9a65981f562ffcb40"
        )

    def run_repair(self, bug_info, repair_config_info):
        super(APRER, self).run_repair(bug_info, repair_config_info)
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        subject = join(self.dir_expr,  bug_info["subject"])
        bugid =   bug_info["bug_id"]
        dir_java_src =  bug_info["source_directory"]
        dir_test_src =  bug_info["test_directory"]
        dir_java_bin =  bug_info["class_directory"]
        dir_test_bin =  bug_info["test_class_directory"]
        passing_test_list =  bug_info["passing_test"]
        failing_test_list = bug_info["failing_test"]
        patch_directory = self.dir_output

        # execute repair tool
        command = (
            f"python3 start.py "
            f" {subject} "
            f" {bugid} "
            f" {dir_java_src} "
            f" {dir_test_src} "
            f" {dir_java_bin} "
            f" {dir_test_bin} "
            f" {passing_test_list} "
            f" {failing_test_list} "
            f" {patch_directory} "            
        )
        
        self.timestamp_log_start()
        status = self.run_command(command, log_file_path=self.log_output_path)
        self.process_status(status)
        self.timestamp_log_end()
