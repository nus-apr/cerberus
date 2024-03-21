import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class GenProg(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/genprog"
        self.fix_file = ""

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        if self.is_instrument_only:
            return
        task_conf_id = task_config_info[self.key_id]
        passing_test_identifiers_list = bug_info[self.key_passing_test_identifiers]
        failing_test_identifiers_list = bug_info[self.key_failing_test_identifiers]
        bug_id = str(bug_info[self.key_bug_id])
        self.fix_file = bug_info[self.key_localization][0][self.key_fix_file]

        fix_location = bug_info[self.key_localization][0][self.key_fix_lines][0]
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )
        count_pass = len(passing_test_identifiers_list)
        count_neg = len(failing_test_identifiers_list)
        repair_config_str = (
            "--program {program}\n"
            "--pos-tests {p_size}\n"
            "--neg-tests {n_size}\n"
            "--test-script bash {dir_exp}/test.sh\n".format(
                p_size=count_pass,
                n_size=count_neg,
                dir_exp=self.dir_expr,
                program="{}.cil.i".format(
                    join(self.dir_expr, "src", bug_info[self.key_bin_path])
                ),
            )
        )
        if fix_location:
            target_path = join(self.dir_expr, "src", "fault-loc")
            self.write_file(fix_location, target_path)
            repair_config_str += "--fault-scheme line\n" "--fault-file fault-loc\n"

        self.append_file(repair_config_str, join(self.dir_expr, "src", "repair.conf"))

        save_command = "mkdir {}; cp {} {}".format(
            join(self.dir_expr, "orig"),
            join(self.dir_expr, "src", self.fix_file),
            join(self.dir_expr, "orig"),
        )
        self.run_command(save_command, self.log_output_path, join(self.dir_expr, "src"))

        self.timestamp_log_start()

        repair_command = 'bash -c \'export PATH="/root/.opam/4.12.0/bin/:$PATH"; timeout -k 5m {}h  '.format(
            str(timeout)
        )
        repair_command += "genprog --label-repair --continue "
        repair_command += " repair.conf'"
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_expr + "/src"
        )

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
        dir_results = dir_info["result"]
        dir_patch = join(self.dir_expr, "src", "..")
        copy_command = "cp -rf {} {}".format(dir_patch, self.dir_output)
        self.run_command(copy_command, "/dev/null", self.dir_expr)

        dir_preprocessed = join(self.dir_expr, "src", "preprocessed")
        copy_command = "cp -rf {} {}/preprocessed".format(
            dir_preprocessed, self.dir_output
        )
        self.run_command(copy_command, "/dev/null", self.dir_expr)

        dir_coverage = join(self.dir_expr, "src", "coverage")
        copy_command = "cp -rf {} {}/coverage".format(dir_coverage, self.dir_output)
        self.run_command(copy_command, "/dev/null", self.dir_expr)

        patch_id = 0
        dir_repair_local = join(
            self.dir_output, "..", "".join(self.fix_file.split("/")[:-1])
        )
        dir_patch_local = self.dir_output + "/patches"
        if self.is_dir(dir_repair_local):
            output_patch_list = [
                f
                for f in self.list_dir(dir_repair_local)
                if self.is_file(join(dir_repair_local, f)) and ".c" in f
            ]
            for f in output_patch_list:
                patched_source = dir_repair_local + "/" + f
                patch_id_candidate = str(f).split("-")[-1]
                if not str(patch_id).isnumeric():
                    patch_id = 0
                else:
                    patch_id = int(patch_id_candidate)
                patch_file = dir_patch_local + "/" + str(patch_id) + ".patch"
                diff_command = (
                    "diff -U 0 /tmp/orig.c "
                    + patched_source
                    + "> {}".format(patch_file)
                )
                self.run_command(diff_command)
                del_command = "rm -f" + patched_source
                self.run_command(del_command)
            save_command = "cp -rf " + dir_patch_local + " " + dir_results
            self.run_command(save_command)
        super(GenProg, self).save_artifacts(dir_info)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
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
        is_interrupted = True
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = log_lines[0].replace("\n", "")
        self.stats.time_stats.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "variant " in line:
                self.stats.patch_stats.enumerations = int(
                    line.split("/")[0].split(" ")[-1]
                )
            elif "possible edits" in line:
                self.stats.patch_stats.generated = int(
                    line.split(": ")[2].split(" ")[0]
                )
            elif "fails to compile" in line:
                self.stats.patch_stats.non_compilable += 1
            elif "Repair Found" in line:
                self.stats.patch_stats.plausible += 1
            elif "cilrep done serialize" in line:
                is_interrupted = False

        if self.stats.patch_stats.generated == 0:
            if self.is_file(dir_results + "/coverage.path"):
                # TODO
                if os.path.getsize(dir_results + "/coverage.path"):
                    self.emit_error("[error] error detected in coverage")
            else:
                self.emit_error("[error] error detected in coverage")
        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_interrupted:
            self.emit_warning("[warning] program interrupted before starting repair")

        return self.stats
