import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class StudentFuzzer(AbstractFuzzTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "student-fuzzer"

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> FuzzToolStats:
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
            if not output:
                self.error_exit("failed to get time of crash")
            stdout, stderr = output
            if stdout:
                self.stats.fuzzing_stats.time_to_bug = int(stdout) - self.stime
        else:
            self.stats.fuzzing_stats.time_to_bug = -1

        return self.stats

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        self.emit_normal("executing fuzz command")
        self.nonce = "12345"

        timeout_mins = int(float(task_config_info[self.key_timeout]) * 60)

        self.run_command(
            "bash -c 'cp -Rf {} /home/student/'".format(join(self.dir_expr, "."))
        )

        command_str = f"date +%s"
        exit_code, output = self.exec_command(command_str, dir_path="/home/student")
        if not output:
            self.error_exit("failed to get start time")
        stdout, stderr = output
        if stdout:
            self.stime = int(stdout)

        self.timestamp_log_start()

        fuzz_command = "bash -c 'NONCE={} python3 student_fuzzer.py'".format(
            self.nonce,
        )

        status = self.run_command(fuzz_command, self.log_output_path, "/home/student/")

        self.process_status(status)

        self.timestamp_log_end()
