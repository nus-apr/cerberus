import os
import re
from os.path import join

from app.drivers.tools.slice.AbstractSliceTool import AbstractSliceTool


class AutoBug(AbstractSliceTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/autobug"
        self.id = ""

    def instrument_program(self, config_script, build_script, binary_path):
        self.emit_normal("re-running configuration")
        instrument_script_path = self.dir_expr + "/autobug-instrumentation"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f'CFLAGS="-fPIC -pie -O0 -g3" CXXFLAGS="-fPIC -pie -O0 -g3" {config_script} {self.dir_expr}\n',
                f'CFLAGS="-fPIC -pie -O0 -g3" CXXFLAGS="-fPIC -pie -O0 -g3" {build_script} {self.dir_expr}\n',
                f"cp {binary_path} {binary_path}.orig\n",
                f"cd /opt/autobug && e9tool -CFR -100 -M true -P 'entry((static int64_t)addr)@autobug' {binary_path}.orig -o {binary_path}\n",
            ],
            instrument_script_path,
        )
        instrument_command = "bash {}".format(instrument_script_path)
        log_instrument_path = join(self.dir_logs, f"{self.name}-instrument.log")
        self.run_command(instrument_command, log_file_path=log_instrument_path)

    def run_slicing(self, bug_info, validate_config_info):
        config_script = bug_info.get(self.key_config_script, None)
        build_script = bug_info.get(self.key_build_script, None)
        binary_path = bug_info.get(self.key_bin_path, None)
        crash_command = bug_info.get(self.key_crash_cmd, None)

        if not config_script:
            self.error_exit(f"{self.name} requires a configuration script as input")
        if not build_script:
            self.error_exit(f"{self.name} requires a build script as input")
        if not binary_path:
            self.error_exit(f"{self.name} requires a binary path as input")
        if not crash_command:
            self.error_exit(f"{self.name} requires a crash command as input")

        build_script_path = join(self.dir_setup, build_script)
        config_script_path = join(self.dir_setup, config_script)
        abs_binary_path = join(self.dir_expr, "src", binary_path)

        self.instrument_program(config_script_path, build_script_path, abs_binary_path)
        super(AutoBug, self).run_slicing(bug_info, validate_config_info)

        if "$POC" in crash_command:
            exploit_list = bug_info.get(self.key_exploit_list, None)
            if not exploit_list:
                self.error_exit(f"{self.name} requires an exploit list as input")
            crash_command = crash_command.replace(
                "$POC", f"{self.dir_setup}/{exploit_list[0]}"
            )

        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        self.id = bug_id
        timeout = str(validate_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = validate_config_info[self.key_tool_params]
        self.timestamp_log_start()
        slice_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h {1} {2} ".format(
                timeout, abs_binary_path, crash_command
            )
            + additional_tool_param
            + "'"
        )

        status = self.run_command(
            slice_command, self.log_output_path, dir_path="/opt/autobug"
        )
        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
