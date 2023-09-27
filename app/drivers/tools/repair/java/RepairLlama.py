import os
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool

class RepairLlama(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(RepairLlama, self).__init__(self.name)
        self.image_name = "rshariffdeen/astor"
        self.hash_digest = ""
        
    def run_repair(self, bug_info, repair_config_info):
        super(RepairLlama, self).run_repair(bug_info, repair_config_info)
        '''
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        '''
        # execute repair tool
        self.timestamp_log_start()
        print(bug_info)
        
        print(repair_config_info)
        dir_java_src = join(self.dir_expr, "src", bug_info["source_directory"])
        dir_test_src = join(self.dir_expr, "src", bug_info["test_directory"])
        dir_java_bin = join(self.dir_expr, "src", bug_info["class_directory"])
        dir_test_bin = join(self.dir_expr, "src", bug_info["test_class_directory"])

        print(bug_info["source_file"])
        print(bug_info["line_numbers"])        
        # repair_command = ""
        # status = self.run_command(repair_command,
        #                           log_file_path=self.log_output_path)
        # self.process_status(status)
        self.timestamp_log_end()
    
    def save_artefacts(self, dir_info):
        pass

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal.normal("\t\t\t analysing output of " + self.name)
        return self.stats