import os
import re
from os import listdir
from os.path import isfile
from os.path import join

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.utilities import error_exit
from app.drivers.tools.AbstractTool import AbstractTool


class Angelix(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Angelix, self).__init__(self.name)
        self.image_name = "mechtaev/angelix:1.1"

    def repair(self, bug_info, config_info):
        super(Angelix, self).repair(
            bug_info,
            config_info,
        )
        if values.only_instrument:
            return
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        source_file = str(bug_info[definitions.KEY_FIX_FILE])
        fix_line_number_list = bug_info[definitions.KEY_FIX_LINES]
        fix_location = bug_info[definitions.KEY_FIX_LOC]
        timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        failing_test_list = bug_info[definitions.KEY_FAILING_TEST]
        passing_test_list = bug_info[definitions.KEY_PASSING_TEST]
        subject_name = bug_info[definitions.KEY_SUBJECT]
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        src_path = join(self.dir_expr, "src")
        gold_path = join(self.dir_expr, "src-gold")
        angelix_dir_path = join(self.dir_expr, "angelix")
        oracle_path = join(angelix_dir_path, "oracle")
        config_script_path = join(angelix_dir_path, "config")
        build_script_path = join(angelix_dir_path, "build")
        timeout_s = int(timeout) * 3600
        syn_timeout = int(0.25 * timeout_s * 1000)
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + " "
        if passing_test_list:
            filtered_list = self.filter_tests(passing_test_list, subject_name, bug_id)
            for test_id in filtered_list:
                test_id_list += test_id + " "

        arguments = [
            "--configure {}".format(config_script_path),
            "--golden {}".format(gold_path),
            "--build {}".format(build_script_path),
            # "--output patches "
            "--synthesis-timeout {}".format(str(syn_timeout)),
        ]

        if fix_location:
            arguments.append(" --lines {0}  ".format(",".join(fix_line_number_list)))

        if values.dump_patches:
            arguments.append(" --dump-patches ")

        if os.path.isfile("/tmp/ANGELIX_ARGS"):
            with open("/tmp/ANGELIX_ARGS", "r") as arg_file:
                arg_line = arg_file.readline()
                arguments.append(arg_line.strip())
            os.remove("/tmp/ANGELIX_ARGS")
        if os.path.isfile("/tmp/ANGELIX_KLEE_LOAD"):
            with open("/tmp/ANGELIX_KLEE_LOAD", "r") as arg_file:
                load_line = arg_file.readline()
                os.system("export ANGELIX_KLEE_LOAD={}".format(load_line.strip()))
            os.remove("/tmp/ANGELIX_KLEE_LOAD")
        arguments.append(
            "  --generate-all {0} "
            " --timeout {1}".format(additional_tool_param, str(timeout_s))
        )

        repair_command = "bash -c 'source /angelix/activate && timeout -k 5m {}h  angelix {} {} {} {} {}'".format(
            str(timeout),
            src_path,
            source_file,
            oracle_path,
            test_id_list,
            " ".join(arguments),
        )
        self.timestamp_log_start()
        status = self.run_command(repair_command, self.log_output_path, self.dir_expr)
        self.timestamp_log_end()
        if status != 0:
            emitter.warning(
                "\t\t\t[warning] {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t[success] {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        emitter.normal("\t\t\t saving artifacts of " + self.name)
        # dir_artifact = dir_info["artifact"]
        # execute_command("rm /tmp/find_dir")
        # dir_patch = join(self.dir_expr, "patches")
        # copy_command = "cp -rf {} {}".format(dir_patch, dir_artifact)
        # self.run_command(copy_command, "/dev/null", self.dir_expr)
        # copy_command = "docker cp " + container_id + ":" + dir_expr + "src/" + source_file + " /tmp/orig_angelix.c"
        # execute_command(copy_command)
        #
        # dir_patch_local = dir_output + "/patches"
        if self.container_id:
            container.fix_permissions(self.container_id, "/output")
        # if os.path.isdir(dir_patch_local):
        #     output_patch_list = [f for f in listdir(dir_patch_local) if isfile(join(dir_patch_local, f)) and ".patch" in f]
        #     for f in output_patch_list:
        #         context_patch = dir_patch_local + "/" + f
        #         patched_source = "/tmp/applied"
        #         patch_command = "patch /tmp/orig_angelix.c {} -o {}".format(context_patch, patched_source)
        #         execute_command(patch_command)
        #         patch_id = str(f).split(".")[0]
        #         patch_file = dir_patch_local + "/" + str(patch_id) + "_angelix.patch"
        #         diff_command = "diff -U 0 /tmp/orig.c " + patched_source + "> {}".format(patch_file)
        #         execute_command(diff_command)
        #         del_command = "rm -f {} {}".format(patched_source, context_patch)
        #         execute_command(del_command)
        #     save_command = "cp -rf " + dir_patch_local + " " + dir_results
        #     execute_command(save_command)

        super(Angelix, self).save_artifacts(dir_info)

    def instrument(self, bug_info):
        """instrumentation for the experiment as needed by the tool"""
        emitter.normal("\t\t\t instrumenting for " + self.name)
        bug_id = bug_info[definitions.KEY_BUG_ID]
        conf_id = str(values.current_profile_id)
        buggy_file = bug_info[definitions.KEY_FIX_FILE]
        self.log_instrument_path = (
            self.dir_logs
            + "/"
            + conf_id
            + "-"
            + self.name
            + "-"
            + bug_id
            + "-instrument.log"
        )
        command_str = "bash instrument.sh {} {}".format(self.dir_expr, buggy_file)
        status = self.run_command(command_str, self.log_instrument_path, self.dir_inst)
        if status not in [0, 126]:
            error_exit(
                "error with instrumentation of "
                + self.name
                + "; exit code "
                + str(status)
            )
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        is_error = False
        count_plausible = 0
        count_enumerations = 0
        conf_id = str(values.current_profile_id)
        self.log_analysis_path = join(
            self.dir_logs,
            "{}-{}-{}-analysis.log".format(conf_id, self.name.lower(), bug_id),
        )
        return self._space, self._time, self._error
        dir_results = dir_info["result"]
        regex = re.compile("(.*-output.log$)")
        for _, _, files in os.walk(dir_results):
            for file in files:
                if regex.match(file) and self.name in file:
                    self.log_output_path = dir_results + "/" + file
                    break
        count_non_compilable = 0
        count_plausible = 0
        size_search_space = 0
        count_enumerations = 0
        time_duration = 0
        if not self.log_output_path or not os.path.isfile(self.log_output_path):
            emitter.warning("\t\t\t[warning] no log file found")
            return (
                size_search_space,
                count_enumerations,
                count_plausible,
                count_non_compilable,
                time_duration,
            )
        emitter.highlight("\t\t\t Log File: " + self.log_output_path)
        is_error = False
        is_timeout = True
        reported_fail_list = set()
        time_duration = 0
        if os.path.isfile(self.log_output_path):
            with open(self.log_output_path, "r") as log_file:
                log_lines = log_file.readlines()
                time_start = log_lines[0].rstrip()
                time_end = log_lines[-1].rstrip()
                time_duration = self.time_duration(time_start, time_end)
                collect_neg = False
                for line in log_lines:
                    if "selected expressions" in line:
                        size_search_space = size_search_space + 1
                    elif "considering suspicious expressions" in line:
                        count_enumerations = count_enumerations + 1
                    elif "repair test suite: []" in line:
                        is_error = True
                        emitter.warning("\t\t\t\t[warning] repair test suite: []")
                    elif "validation test suite: []" in line:
                        is_error = True
                        emitter.warning("\t\t\t\t[warning] validation test suite: []")
                    elif "No negative test exists" in line:
                        is_error = True
                        is_timeout = False
                        emitter.warning("\t\t\t\t[warning] No negative test exists")
                    elif "no patch generated" in line:
                        is_timeout = False
                        count_plausible = 0
                    elif "patches successfully generated" in line:
                        is_timeout = False
                    elif "running negative tests" in line:
                        collect_neg = True
                    elif "excluding test" in line:
                        removing_test_id = line.split("excluding test ")[-1].split(" ")[
                            0
                        ]
                        if removing_test_id in reported_fail_list:
                            reported_fail_list.remove(removing_test_id)
                    elif "failed to build" in line and "golden" in line:
                        is_error = True
                        emitter.error("\t\t\t\t[error] failed to build golden")
                    elif "failed to build" in line and "validation" in line:
                        is_error = True
                        emitter.error("\t\t\t\t[error] failed to build validation")
                    elif "failed to build" in line and "frontend" in line:
                        is_error = True
                        emitter.error("\t\t\t\t[error] failed to build frontend")
                    elif collect_neg and "running test" in line:
                        t_id = (
                            line.split("running test ")[-1]
                            .split(" ")[0]
                            .replace("'", "")
                        )
                        reported_fail_list.add(t_id)
                    elif collect_neg and "repair test suite" in line:
                        collect_neg = False
                log_file.close()
        if is_timeout:
            count_enumerations = count_enumerations - 1
        dir_patch = dir_results + "/patches"
        if dir_patch and os.path.isdir(dir_patch):
            output_patch_list = [
                f for f in listdir(dir_patch) if isfile(join(dir_patch, f))
            ]
            count_plausible = len(output_patch_list)
        count_implausible = count_enumerations - count_plausible - count_non_compilable
        if list(reported_fail_list) != fail_list:
            emitter.warning("\t\t\t\t[warning] unexpected failing test-cases reported")
            emitter.warning(
                "\t\t\t\texpected fail list: {0}".format(",".join(fail_list))
            )
            reported_list_str = ",".join(list(reported_fail_list))
            if len(reported_fail_list) > 10:
                reported_list_str = ",".join(list(reported_fail_list)[:10]) + "..."
            emitter.warning("\t\t\t\treported fail list: {0}".format(reported_list_str))
        if is_error:
            emitter.error("\t\t\t\t[error] error detected in logs")
        if is_timeout:
            emitter.warning("\t\t\t\t[warning] timeout before ending")
        with open(self.log_analysis_path, "w") as log_file:
            log_file.write("\t\t search space size: {0}\n".format(size_search_space))
            if values.dump_patches:
                count_enumerations = count_plausible
            else:
                log_file.write(
                    "\t\t count plausible patches: {0}\n".format(count_plausible)
                )
                log_file.write(
                    "\t\t count non-compiling patches: {0}\n".format(
                        count_non_compilable
                    )
                )
                log_file.write(
                    "\t\t count implausible patches: {0}\n".format(count_implausible)
                )
            log_file.write("\t\t count enumerations: {0}\n".format(count_enumerations))
            log_file.write("\t\t any errors: {0}\n".format(is_error))
            log_file.write("\t\t time duration: {0} seconds\n".format(time_duration))
        return (
            size_search_space,
            count_enumerations,
            count_plausible,
            count_non_compilable,
            time_duration,
        )

    def filter_tests(self, test_id_list, subject, bug_id):
        filtered_list = []
        filter_list = []
        if str(subject).lower() == "gzip":
            filter_list = []
            if bug_id == "884ef6d16c":
                filter_list.extend([4, 11])

        # elif str(subject).lower() == "php":
        #     filter_list = []
        #     if bug_id == "5bb0a44e06":
        #         filter_list.extend([5553, 6548, 9563, 280, 3471])
        #     elif bug_id == "0927309852":
        #         filter_list.extend([7384, 7440, 7551, 7511, 7527, 7639, 9563, 7780])

        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return filtered_list
