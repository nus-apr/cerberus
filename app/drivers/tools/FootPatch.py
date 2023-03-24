import os
import re
from datetime import datetime
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class FootPatch(AbstractTool):
    relative_binary_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(FootPatch, self).__init__(self.name)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        emitter.normal("\t\t\t preparing subject for repair with " + self.name)
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
        analysis_command = (
            "~/footpatch/infer-linux64-v0.9.3/infer/bin/infer  "
            "-j 20 --headers --no-filtering -- make -j20"
        )
        self.run_command(analysis_command, dir_path=dir_src, env=new_env)
        emitter.normal(
            "\t\t\t preparation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )

    def repair(self, bug_info, config_info):
        self.prepare(bug_info)
        super(FootPatch, self).repair(bug_info, config_info)
        if values.only_instrument:
            return
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )

        if values.use_container:
            emitter.error(
                "[Exception] unimplemented functionality: FootPatch docker support not implemented"
            )
            error_exit("Unhandled Exception")

        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        new_env = os.environ.copy()
        if "DUMP_CANDS" in new_env:
            del new_env["DUMP_CANDS"]
        new_env["GLOBAL_REPAIR"] = "1"

        self.timestamp_log_start()
        footpatch_command = (
            "timeout -k 5m {0}h ~/footpatch/infer-linux64-v0.9.3/infer/bin/infer "
            "-j 20 --headers --no-filtering {1} "
            "-- make -j20".format(timeout_h, additional_tool_param)
        )

        status = self.run_command(
            footpatch_command,
            dir_path=dir_src,
            env=new_env,
            log_file_path=self.log_output_path,
        )
        if status != 0:
            emitter.warning(
                "\t\t\t[warning] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        copy_command = "cp -rf {}/src/infer-out/footpatch {}".format(
            self.dir_expr, self.dir_output
        )
        self.run_command(copy_command)
        super(FootPatch, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id.get("NA"))
        self.log_analysis_path = join(
            self.dir_logs,
            "{}-{}-{}-analysis.log".format(conf_id, self.name.lower(), bug_id),
        )

        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break

        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t[warning] no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
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
                emitter.error("\t\t\t\t[error] error detected in logs")

        return self._space, self._time, self._error
