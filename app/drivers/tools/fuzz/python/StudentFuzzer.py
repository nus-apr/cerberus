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

        r = self.list_dir("/home/student", regex="*")
        self.emit_normal(f"saw files {r}")

        if f"/home/student/{self.nonce}.crash" in r:
            command_str = f"date -r {self.nonce}.crash +%s"
            exit_code, output = self.exec_command(
                command_str, dir_path="/home/student/"
            )
            stdout, stderr = output
            if stdout:
                self.stats.fuzzing_stats.time_to_bug = int(stdout) - self.stime
        else:
            self.stats.fuzzing_stats.time_to_bug = -1

        return self.stats

    def run_fuzz(self, bug_info, fuzz_config_info):
        super(StudentFuzzer, self).run_fuzz(bug_info, fuzz_config_info)
        self.emit_normal("executing fuzz command")
        self.nonce = "12345"

        timeout_mins = int(float(fuzz_config_info[self.key_timeout]) * 60)

        self.run_command(
            "bash -c 'cp -Rf {} /home/student/'".format(join(self.dir_expr, "."))
        )

        command_str = f"date +%s"
        exit_code, output = self.exec_command(command_str, dir_path="/home/student")
        stdout, stderr = output
        if stdout:
            self.stime = int(stdout)

        self.timestamp_log_start()

        repair_command = "bash -c 'NONCE={} python3 student_fuzzer.py'".format(
            self.nonce,
        )

        status = self.run_command(
            repair_command, self.log_output_path, "/home/student/"
        )

        self.process_status(status)

        self.timestamp_log_end()
