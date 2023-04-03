import os
import re
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.drivers.tools.AbstractTool import AbstractTool


class CRepair(AbstractTool):

    error_messages = ["aborted", "core dumped", "runtime error", "segmentation fault"]

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(CRepair, self).__init__(self.name)
        self.image_name = "rshariffdeen/crepair:tool"

    def generate_conf_file(self, bug_info):
        repair_conf_path = join(self.dir_setup, "crepair", "repair.conf")
        conf_content = []
        poc_list = bug_info[definitions.KEY_EXPLOIT_LIST]
        poc_abs_list = [join(self.dir_setup, x) for x in poc_list]

        conf_content.append("dir_exp:{}\n".format(self.dir_expr))
        conf_content.append("tag_id:{}\n".format(bug_info[definitions.KEY_BUG_ID]))
        conf_content.append("src_directory:src\n")
        conf_content.append(
            "binary_path:{}\n".format(bug_info[definitions.KEY_BINARY_PATH])
        )
        conf_content.append(
            "config_command:CC=crepair-cc CXX=crepair-cxx {}\n".format(
                self.dir_setup + "/config.sh /experiment"
            )
        )
        conf_content.append(
            "build_command:CC=crepair-cc CXX=crepair-cxx {}\n".format(
                self.dir_setup + "/build.sh /experiment"
            )
        )
        conf_content.append(
            "test_input_list:{}\n".format(bug_info[definitions.KEY_CRASH_CMD])
        )
        conf_content.append("poc_list:{}\n".format(",".join(poc_abs_list)))
        self.append_file(conf_content, repair_conf_path)
        return repair_conf_path

    def repair(self, bug_info, config_info):
        super(CRepair, self).repair(bug_info, config_info)
        timeout_h = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        # repair_conf_path = self.generate_conf_file(bug_info)
        repair_conf_path = self.dir_setup + "/crepair/repair.conf"
        bug_json_path = self.dir_expr + "/bug.json"
        self.timestamp_log_start()
        repair_command = (
            f"bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {str(timeout_h)}h "
            f"crashrepair repair --no-fuzz {bug_json_path} {additional_tool_param}'"
        )

        status = self.run_command(repair_command, log_file_path=self.log_output_path)
        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
        self.timestamp_log_end()

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        tool_log_dir = "/CrashRepair/logs/"
        tool_log_files = [
            "{}/{}".format(tool_log_dir, f)
            for f in self.list_dir(tool_log_dir)
            if ".log" in f
        ]
        list_artifact_dirs = [self.dir_expr + "/" + x for x in ["analysis", "patches"]]
        list_artifact_files = [
            self.dir_expr + "/" + x for x in ["candidates.json", "bug.json"]
        ]
        for f in tool_log_files + list_artifact_files:
            copy_command = f"cp {f} {self.dir_output}"
            self.run_command(copy_command)
        for d in list_artifact_dirs:
            copy_command = f"cp -rf {d} {self.dir_output}"
            self.run_command(copy_command)
        super(CRepair, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)

        count_plausible = 0
        count_enumerations = 0
        count_compile_errors = 0
        search_space = 0

        # count number of patch files
        self._space.generated = len(
            self.list_dir(
                join(
                    self.dir_expr,
                    "patch-valid" if values.use_valkyrie else "patches",
                )
            )
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Output Log File: " + self.log_output_path)

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "evaluating candidate patch" in line:
                    count_enumerations += 1
                if "writing" in line and "mutations" in line:
                    search_space = int(
                        re.search(r"writing (.*) mutations", line).group(1)
                    )
                elif "saving successful patch" in line:
                    count_plausible += 1
                elif "failed to compile" in line:
                    count_compile_errors += 1

                if any(err in line.lower() for err in self.error_messages):
                    self._error.is_error = True

        self._space.non_compilable = count_compile_errors
        self._space.plausible = count_plausible
        self._space.enumerations = count_enumerations
        self._space.size = search_space
        return self._space, self._time, self._error
