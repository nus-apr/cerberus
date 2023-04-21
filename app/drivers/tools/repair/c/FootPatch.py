import os
import re
from datetime import datetime
from os.path import join

from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class FootPatch(AbstractRepairTool):
    relative_binary_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        self.emit_normal(" preparing subject for repair with " + self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)

        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        new_env = os.environ.copy()
        if "GLOBAL_REPAIR" in new_env:
            del new_env["GLOBAL_REPAIR"]
        new_env["DUMP_CANDS"] = "1"
        time = datetime.now()
        analysis_command = "footpatch " "-j 20 --headers --no-filtering -- make -j20"
        self.run_command(analysis_command, dir_path=dir_src, env=new_env)
        self.emit_normal(
            " preparation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def run_repair(self, bug_info, repair_config_info):
        self.prepare(bug_info)
        super(FootPatch, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return
        repair_conf_id = repair_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        if self.use_container:
            self.error_exit(
                "unimplemented functionality: FootPatch docker support not implemented"
            )

        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        new_env = os.environ.copy()
        if "DUMP_CANDS" in new_env:
            del new_env["DUMP_CANDS"]
        new_env["GLOBAL_REPAIR"] = "1"

        self.timestamp_log_start()
        footpatch_command = (
            "timeout -k 5m {0}h footpatch "
            "-j 20 --headers --no-filtering {1} "
            "-- make -j20".format(timeout_h, additional_tool_param)
        )

        status = self.run_command(
            footpatch_command,
            dir_path=dir_src,
            env=new_env,
            log_file_path=self.log_output_path,
        )

        self.process_status(status)

        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        copy_command = "cp -rf {}/src/infer-out/footpatch {}".format(
            self.dir_expr, self.dir_output
        )
        self.run_command(copy_command)
        super(FootPatch, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")
        dir_results = join(self.dir_expr, "result")
        repair_conf_id = str(self.current_repair_profile_id.get("NA"))
        self.log_stats_path = join(
            self.dir_logs,
            "{}-{}-{}-stats.log".format(repair_conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self._space, self._time, self._error

        self.emit_highlight(" Log File: " + self.log_output_path)
        is_error = False

        # count number of patch files
        dir_footpatch = join(self.dir_expr, "src", "infer-out", "footpatch")
        list_patches = self.list_dir(dir_footpatch, regex="*.patch")
        self._space.generated = len(list_patches)

        footpatch_std_out = self.log_output_path
        log_lines = self.read_file(footpatch_std_out, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        footpatch_log_path = join(
            self.dir_expr, "src", "infer-out", "footpatch", "log.txt"
        )
        if self.is_file(footpatch_log_path):
            log_lines = self.read_file(footpatch_log_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Patch routine" in line:
                    self._space.enumerations += 1
                elif "Writing patches" in line:
                    self._space.plausible += 1
                elif "Filtered candidates:" in line:
                    self._space.size += int(line.split(": ")[-1])
            if is_error:
                self.emit_error("[error] error detected in logs")

        return self._space, self._time, self._error
