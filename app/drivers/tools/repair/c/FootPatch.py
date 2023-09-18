import os
import re
from datetime import datetime
from os.path import join

from app.core.utilities import escape_ansi
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class FootPatch(AbstractRepairTool):
    relative_binary_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "rshariffdeen/footpatch"
        super().__init__(self.name)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        self.emit_normal(" preparing subject for repair with " + self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        dir_src = join(self.dir_expr, "src")
        clean_command = "rm /tmp/td_candidates/*; make clean"
        self.run_command(clean_command, dir_path=dir_src)

        new_env = os.environ.copy()
        if "GLOBAL_REPAIR" in new_env:
            del new_env["GLOBAL_REPAIR"]
        new_env["DUMP_CANDS"] = "1"
        time = datetime.now()
        compile_list = bug_info.get(self.key_compile_programs, [])
        analysis_command = (
            "footpatch "
            "-j 20 --headers --no-filtering -- make -j20 {}".format(
                " ".join(compile_list)
            )
        )
        log_analysis_path = join(self.dir_logs, "footpatch-capture-output.log")
        self.run_command(
            analysis_command,
            dir_path=dir_src,
            env=new_env,
            log_file_path=log_analysis_path,
        )
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
        task_conf_id = repair_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(repair_config_info[self.key_timeout])
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        new_env = os.environ.copy()
        if "DUMP_CANDS" in new_env:
            del new_env["DUMP_CANDS"]
        new_env["GLOBAL_REPAIR"] = "1"

        self.timestamp_log_start()
        compile_list = bug_info.get(self.key_compile_programs, [])
        footpatch_command = (
            "timeout -k 5m {0}h footpatch "
            "-j 20 --headers --no-filtering {1} "
            "-- make -j20 {2} ".format(
                timeout_h, additional_tool_param, " ".join(compile_list)
            )
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
        clean_command = "rm /tmp/*footpatch*"
        self.run_command(clean_command, dir_path=dir_src)

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
        regex = re.compile("(.*-output.log$)")
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
        is_error = False

        # count number of patch files
        dir_footpatch = join(self.dir_expr, "src", "infer-out", "footpatch")
        list_patches = self.list_dir(dir_footpatch, regex="*.patch")

        footpatch_std_out = self.log_output_path
        log_lines = self.read_file(footpatch_std_out, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        footpatch_log_path = join(
            self.dir_expr, "src", "infer-out", "footpatch", "log.txt"
        )

        count_enumerations = 0
        count_plausible = 0
        count_candidates = 0

        if self.is_file(footpatch_log_path):
            log_lines = self.read_file(footpatch_log_path, encoding="iso-8859-1")
            for line in log_lines:
                line = escape_ansi(line)
                if "Patch routine" in line:
                    count_enumerations += 1
                elif "Writing patches" in line:
                    count_plausible += 1
                elif "Filtered candidates:" in line:
                    count_candidates += int(line.split(": ")[-1])
            if is_error:
                self.emit_error("[error] error detected in logs")

        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.size = count_candidates
        self.stats.patch_stats.generated = len(list_patches)
        self.stats.error_stats.is_error = is_error

        return self.stats
