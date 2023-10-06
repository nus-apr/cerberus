import os
import re
import subprocess
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class FAVOR(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.dir_root = '/FAVOR/'
        self.image_name = "dongqa/favor:latest"
        self.hash_digest = "sha256:ad25ba1952883ce48d1023e4c0812fdbc6ba575b08c01baae87013d7729d81bf"

    def prepare_for_repair(self, buggy_filepath, buggy_loc, test_case_path):
        # removing comments from source file and extracting the buggy function execute path
        buggy_loc_strs = ' '.join(map(str, buggy_loc))
        buggy_loc_command = f"--bug_loc {buggy_loc_strs}"
        self.emit_normal("preparing for repairing phase")
        prepare_command = "bash -c 'source /root/anaconda3/etc/profile.d/conda.sh && " \
                          "conda activate favor && cd {} && python3 preparing.py --buggy_filepath {} {} --test_case_path {} >> {}'".format(
                            self.dir_root, buggy_filepath, buggy_loc_command, test_case_path, self.log_output_path)

        status = self.run_command(prepare_command, log_file_path=self.log_output_path, dir_path=self.dir_root)
        self.process_status(status)

    def run_repair(self, bug_info, repair_config_info):
        """
             self.dir_logs - directory to store logs
             self.dir_setup - directory to access setup scripts
             self.dir_expr - directory for experiment
             self.dir_output - directory to store artifacts/output
         """
        super(FAVOR, self).run_repair(bug_info, repair_config_info)
        buggy_loc = bug_info.get('line_numbers')
        buggy_filename = bug_info.get('source_file')
        buggy_filename = re.search(r'[^/]+\.(c|cpp)$', buggy_filename).group() if re.search(r'[^/]+\.(c|cpp)$',
                                                                                         buggy_filename) else None
        test_case = bug_info[self.key_exploit_list][0] if len(bug_info[self.key_exploit_list]) != 0 else 'none'
        test_case_path = os.path.join(self.dir_expr, test_case)
        if buggy_filename is None:
            self.emit_error('FAVOR could only fix C/C++ vulnerabilities')

        buggy_file_path = os.path.join(self.dir_setup, 'valkyrie/', buggy_filename)

        if not self.is_file(buggy_file_path):
            self.error_exit("buggy source file not found")

        if buggy_loc is None:
            # if buggy_loc is not provided, favor will employ another vulnerability localization tool to get relevant locs.
            buggy_loc = 0

        self.prepare_for_repair(buggy_file_path, buggy_loc, test_case_path)
        self.timestamp_log_start()
        timeout_h = str(repair_config_info[self.key_timeout])
        favor_command = "bash -c 'source /root/anaconda3/etc/profile.d/conda.sh && cd {} && conda activate favor " \
                        "&& timeout -k 5m {}h sh ./favor.sh >> {}'".format(self.dir_root, timeout_h,
                                                                           self.log_output_path)

        status = self.run_command(
            favor_command,
            log_file_path=self.log_output_path,
            dir_path=self.dir_root,
        )
        self.process_status(status)
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        generate_command = "python3 generate_patch.py"
        status = self.run_command(generate_command,
                                  log_file_path=self.log_output_path,
                                  dir_path=self.dir_root)
        self.process_status(status)
        patch_dir = join(self.dir_output, 'patches')
        copy_command = "cp  {}/patches/*.patch {}".format(
            self.dir_root, patch_dir)
        status = self.run_command(copy_command,
                                  log_file_path=self.log_output_path,
                                  dir_path=self.dir_root)
        self.process_status(status)
        super(FAVOR, self).save_artifacts(dir_info)
        return

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

        is_error = False
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
                if "Generating patch" in line:
                    count_plausible += 1
                    count_enumerations += 1

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.error_stats.is_error = is_error
        return self.stats
