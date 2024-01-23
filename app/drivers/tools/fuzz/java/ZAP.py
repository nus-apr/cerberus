import os
from os.path import join

from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class ZAP(AbstractFuzzTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "jarvx/zap_jenkins:3.0"

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """

        return self.stats

    def run_fuzz(self, bug_info, fuzz_config_info):
        super(ZAP, self).run_fuzz(bug_info, fuzz_config_info)
        self.emit_normal("executing fuzz command")

        timeout = int(float(fuzz_config_info[self.key_timeout]) * 60)
       
        self.timestamp_log_start()

        initial_corpus = join(self.dir_setup, self.name, "initial-corpus")
        
        fuzz_command =  f"/zap/zap-full-scan.py -t http://127.0.0.1:8080/ -m {timeout}"  # timeout is the number of mins # timeout is the number of mins 

        status = self.run_command(
            fuzz_command, self.log_output_path, join(self.dir_expr, "src")
        )

        self.process_status(status)

        self.timestamp_log_end()
