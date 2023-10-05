class LuoJiaFixer(AbstractRepairTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(NewTool, self).__init__(self.name)
        self.image_name = ""
        self.hash_digest = ""

     def run_repair(self, bug_info, repair_config_info):
        super(NewTool, self).repair(bug_info, repair_config_info)
        '''
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        '''
        # execute repair tool
        self.timestamp_log_start()
        repair_command = ""
        status = self.run_command(repair_command,
                                  log_file_path=self.log_output_path)
        self.process_status(status)
        self.timestamp_log_end()

