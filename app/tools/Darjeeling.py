import os
import re
import shutil
from app.tools.AbstractTool import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values, emitter, container
import mmap
from os import listdir
from os.path import isfile, join


class Darjeeling(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Darjeeling, self).__init__(self.name)

    def repair(self, dir_info, experiment_info, config_info, container_id, instrument_only):
        super(Darjeeling, self).repair(dir_info, experiment_info, config_info, container_id, instrument_only)
        if not instrument_only:
            conf_id = config_info[definitions.KEY_ID]
            dir_logs = dir_info["logs"]
            dir_setup = dir_info["setup"]
            dir_expr = dir_info["expr"]
            passing_test_list = experiment_info[definitions.KEY_PASSING_TEST]
            failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
            bug_id = str(experiment_info[definitions.KEY_BUG_ID])
            emitter.normal("\t\t\t running repair with " + self.name)
            fix_file = experiment_info[definitions.KEY_FIX_FILE]
            fix_location = experiment_info[definitions.KEY_FIX_LOC]
            timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
            additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
            self.log_output_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-output.log"
            count_pass = len(passing_test_list)
            count_neg = len(failing_test_list)
            repair_config_str = "--pos-tests {p_size}\n" \
                                "--neg-tests {n_size}\n" \
                                "--test-script bash {dir_exp}/test.sh\n".format(bug_id=bug_id, p_size=count_pass,
                                                                                n_size=count_neg, dir_exp=dir_expr)
            if fix_location:
                source_file, line_number = fix_location.split(":")
                tmp_file = "/tmp/genprog-fault-loc"
                target_path = dir_expr + "/src/fault-loc"
                with open(tmp_file, "w") as loc_file:
                    loc_file.write(str(line_number))
                copy_command = "docker cp {} {}:{}".format(tmp_file,container_id, target_path)
                execute_command(copy_command)
                repair_config_str += "--fault-scheme line\n" \
                                     "--fault-file fault-loc\n"

            if container_id:
                tmp_repair_file = "/tmp/repair.conf"
                repair_conf_path = dir_expr + "/src/repair.conf"
                load_command = "docker cp " + container_id + ":" + repair_conf_path + " " + tmp_repair_file
                execute_command(load_command)
                with open(tmp_repair_file, "a") as conf_file:
                    conf_file.write(repair_config_str)
                save_command = "docker cp " + tmp_repair_file + " " + container_id + ":" + repair_conf_path
                execute_command(save_command)

            else:
                repair_conf_path = dir_expr + "/src/repair.conf"
                with open(repair_conf_path, "a") as conf_file:
                    conf_file.write(repair_config_str)

            save_command = "mkdir {}; cp {} {}".format(dir_expr + "/orig", dir_expr + "/src/" + fix_file,
                                                       dir_expr + "/orig")
            self.run_command(save_command,self.log_output_path, dir_expr + "/src", container_id)
            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') > " + self.log_output_path
            execute_command(timestamp_command)

            repair_command = "timeout -k 5m {1}h  ".format(dir_expr + "/src", str(timeout))
            repair_command += "darjeeling --label-repair --continue "
            repair_command += " repair.conf".format(self.log_output_path)
            status = self.run_command(repair_command, self.log_output_path, dir_expr + "/src", container_id)
            if status != 0:
                emitter.warning("\t\t\t[warning] {0} exited with an error code {1}".format(self.name, status))
            else:
                emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
            emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))
            timestamp_command = "echo $(date '+%a %d %b %Y %H:%M:%S %p') >> " + self.log_output_path
            execute_command(timestamp_command)
        return

    def save_artefacts(self, dir_info, experiment_info, container_id):
        emitter.normal("\t\t\t saving artefacts of " + self.name)
        dir_expr = dir_info["experiment"]
        dir_results = dir_info["result"]
        dir_patch = dir_expr + "/src/repair"
        dir_output = dir_info["output"]
        dir_artifact = dir_info["artifact"]
        copy_command = "cp -rf  " + dir_patch + " " + dir_artifact
        self.run_command(copy_command, "/dev/null", dir_expr, container_id)

        dir_preprocessed = dir_expr + "/src/preprocessed"
        copy_command = "cp -rf  " + dir_preprocessed + " " + dir_artifact + "/preprocessed"
        self.run_command(copy_command, "/dev/null", dir_expr, container_id)

        dir_coverage = dir_expr + "/src/coverage"
        copy_command = "cp -rf  " + dir_coverage + " " + dir_artifact + "/coverage"
        self.run_command(copy_command, "/dev/null", dir_expr, container_id)
        super(Darjeeling, self).save_artefacts(dir_info, experiment_info, container_id)

        fix_file = experiment_info[definitions.KEY_FIX_FILE]
        copy_command = "docker cp " + container_id + ":" + dir_expr + "src/" + fix_file + " /tmp/orig.c"
        execute_command(copy_command)
        patch_id = 0
        dir_repair_local = dir_output + "/repair/" + "".join(fix_file.split("/")[:-1])
        dir_patch_local = dir_output + "/patches"
        container.fix_permissions(container_id, "/output")
        if os.path.isdir(dir_repair_local):
            output_patch_list = [f for f in listdir(dir_repair_local) if isfile(join(dir_repair_local, f)) and ".c" in f]
            for f in output_patch_list:
                patched_source = dir_repair_local + "/" + f
                patch_id = str(f).split("-")[-1]
                if not str(patch_id).isnumeric():
                    patch_id = 0
                patch_file = dir_patch_local + "/" + str(patch_id) + ".patch"
                diff_command = "diff -U 0 /tmp/orig.c " + patched_source + "> {}".format(patch_file)
                execute_command(diff_command)
                del_command = "rm -f" + patched_source
                execute_command(del_command)
            save_command = "cp -rf " + dir_patch_local + " " + dir_results
            execute_command(save_command)

        return

    def analyse_output(self, dir_logs, dir_results, dir_expr, dir_setup, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        conf_id = str(values.CONFIG_ID)
        self.log_analysis_path = dir_logs + "/" + conf_id + "-" + self.name.lower() + "-" + bug_id + "-analysis.log"
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        time_duration = 0
        regex = re.compile('(.*-output.log$)')
        for root, dirs, files in os.walk(dir_results):
            for file in files:
                if regex.match(file):
                    self.log_output_path = dir_results + "/" + file
                    break
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        is_interrupted = True
        with open(self.log_output_path, "r") as log_file:
            log_lines = log_file.readlines()
            time_start = log_lines[0].replace("\n", "")
            time_end = log_lines[-1].replace("\n", "")
            time_duration = self.time_duration(time_start, time_end)
            for line in log_lines:
                if "variant " in line:
                    count_enumerations = int(line.split("/")[0].split(" ")[-1])
                elif "possible edits" in line:
                    size_search_space = line.split(": ")[2].split(" ")[0]
                elif "fails to compile" in line:
                    count_non_compilable = count_non_compilable + 1
                elif "Repair Found" in line:
                    count_plausible = count_plausible + 1
                elif "cilrep done serialize" in line:
                    is_interrupted = False
            log_file.close()
        if size_search_space == 0:
            if os.path.isfile(dir_results + "/coverage.path"):
                if os.path.getsize(dir_results + "/coverage.path"):
                    emitter.error("\t\t\t\t[error] error detected in coverage")
            else:
                emitter.error("\t\t\t\t[error] error detected in coverage")
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_interrupted:
            emitter.warning("\t\t\t\t[warning] program interrupted before starting repair")
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        with open(self.log_analysis_path, 'w') as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if values.DEFAULT_DUMP_PATCHES:
                count_enumerations = count_plausible
            else:
                log_file.write("\t\t count plausible patches: {0}\n".format(count_plausible))
                log_file.write("\t\t count non-compiling patches: {0}\n".format(count_non_compilable))
                log_file.write("\t\t count implausible patches: {0}\n".format(count_implausible))
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
        return size_search_space, count_enumerations, count_plausible, count_non_compilable, time_duration

