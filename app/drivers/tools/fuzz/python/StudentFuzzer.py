import os
from os.path import join

from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class StudentFuzzer(AbstractFuzzTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "student-fuzzer"

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """
        return self.stats

    def run_fuzz(self, bug_info, fuzz_config_info):
        super(StudentFuzzer, self).run_fuzz(bug_info, fuzz_config_info)
        self.emit_normal("executing fuzz command")

        timeout_mins = int(float(fuzz_config_info[self.key_timeout]) * 60)

        self.run_command(
            "bash -c 'cp -rf {} /home/student/'".format(join(self.dir_expr, "src", "*"))
        )

        self.timestamp_log_start()
        repair_command = (
            "bash -c 'NONCE=12345 timeout -k 5m {}m python3 student_fuzzer.py'".format(
                timeout_mins
            )
        )

        status = self.run_command(
            repair_command, self.log_output_path, "/home/student/"
        )

        self.process_status(status)

        self.timestamp_log_end()
