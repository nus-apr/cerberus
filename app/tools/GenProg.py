import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command
from app import definitions, values, emitter
import mmap
from os import listdir
from os.path import isfile, join


class GenProg(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(GenProg, self).__init__(self.name)
        self.image_name = "rshariffdeen/genprog"

    def repair(self, bug_info, config_info):
        super(GenProg, self).repair(bug_info, config_info)
        if values.CONF_INSTRUMENT_ONLY:
            return
        conf_id = config_info[definitions.KEY_ID]
        passing_test_list = bug_info[definitions.KEY_PASSING_TEST]
        failing_test_list = bug_info[definitions.KEY_FAILING_TEST]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        emitter.normal("\t\t\t running repair with " + self.name)
        fix_file = bug_info[definitions.KEY_FIX_FILE]
        fix_location = bug_info[definitions.KEY_FIX_LINES][0]
        timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        count_pass = len(passing_test_list)
        count_neg = len(failing_test_list)
        repair_config_str = (
            "--pos-tests {p_size}\n"
            "--neg-tests {n_size}\n"
            "--test-script bash {dir_exp}/test.sh\n".format(
                bug_id=bug_id,
                p_size=count_pass,
                n_size=count_neg,
                dir_exp=self.dir_expr,
            )
        )
        if fix_location:
            target_path = join(self.dir_expr, "src", "fault-loc")
            self.write_file(fix_location, target_path)
            repair_config_str += "--fault-scheme line\n" "--fault-file fault-loc\n"

        self.write_file(repair_config_str, join(self.dir_expr, "src", "repair.conf"))

        save_command = "mkdir {}; cp {} {}".format(
            join(self.dir_expr + "orig"),
            join(self.dir_expr, "src", fix_file),
            join(self.dir_expr + "orig"),
        )
        self.run_command(save_command, self.log_output_path, join(self.dir_expr, "src"))

        self.timestamp_log()

        repair_command = "timeout -k 5m {1}h  ".format(
            join(self.dir_expr, "src"), str(timeout)
        )
        repair_command += "genprog --label-repair --continue "
        repair_command += " repair.conf".format(self.log_output_path)
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_expr + "/src"
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
        self.timestamp_log()

    def save_artefacts(self, dir_info):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_results = dir_info["result"]
        dir_patch = self.dir_expr + "/src/repair"
        dir_output = dir_info["output"]
        dir_artifact = dir_info["artifact"]
        copy_command = "cp -rf  " + dir_patch + " " + dir_artifact
        self.run_command(
            copy_command,
            "/dev/null",
            self.dir_expr,
        )

        dir_preprocessed = join(self.dir_expr, "src", "preprocessed")
        copy_command = "cp -rf {} {}/preprocessed".format(
            dir_preprocessed, dir_artifact
        )
        self.run_command(
            copy_command,
            "/dev/null",
            self.dir_expr,
        )

        dir_coverage = join(self.dir_expr, "src", "coverage")
        copy_command = "cp -rf {} {}/coverage".format
        (dir_coverage, dir_artifact)
        self.run_command(
            copy_command,
            "/dev/null",
            self.dir_expr,
        )
        super(GenProg, self).save_artefacts(dir_info)

        fix_file = experiment_info[definitions.KEY_FIX_FILE]
        copy_command = (
            "docker cp " + +":" + self.dir_expr + "src/" + fix_file + " /tmp/orig.c"
        )
        execute_command(copy_command)
        patch_id = 0
        dir_repair_local = dir_output + "/repair/" + "".join(fix_file.split("/")[:-1])
        dir_patch_local = dir_output + "/patches"
        if os.path.isdir(dir_repair_local):
            output_patch_list = [
                f
                for f in listdir(dir_repair_local)
                if isfile(join(dir_repair_local, f)) and ".c" in f
            ]
            for f in output_patch_list:
                patched_source = dir_repair_local + "/" + f
                patch_id = str(f).split("-")[-1]
                if not str(patch_id).isnumeric():
                    patch_id = 0
                patch_file = dir_patch_local + "/" + str(patch_id) + ".patch"
                diff_command = (
                    "diff -U 0 /tmp/orig.c "
                    + patched_source
                    + "> {}".format(patch_file)
                )
                execute_command(diff_command)
                del_command = "rm -f" + patched_source
                execute_command(del_command)
            save_command = "cp -rf " + dir_patch_local + " " + dir_results
            execute_command(save_command)

        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.CONFIG_ID)
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
        is_interrupted = True
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "variant " in line:
                self._space.enumerations = int(line.split("/")[0].split(" ")[-1])
            elif "possible edits" in line:
                self._space.generated = line.split(": ")[2].split(" ")[0]
            elif "fails to compile" in line:
                self._space.non_compilable += 1
            elif "Repair Found" in line:
                self._space.plausible += 1
            elif "cilrep done serialize" in line:
                is_interrupted = False

        if self._space.generated == 0:
            if self.is_file(dir_results + "/coverage.path"):
                # TODO
                if os.path.getsize(dir_results + "/coverage.path"):
                    emitter.error("\t\t\t\t[error] error detected in coverage")
            else:
                emitter.error("\t\t\t\t[error] error detected in coverage")
        if self._error.is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_interrupted:
            emitter.warning(
                "\t\t\t\t[warning] program interrupted before starting repair"
            )

        return self._space, self._time, self._error
