import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List
from typing import Set

from app.core import container
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class Angelix(AbstractRepairTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mechtaev/angelix:1.1"

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        if self.is_instrument_only:
            return
        task_conf_id = task_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        source_file = str(bug_info[self.key_localization][0][self.key_fix_file])
        fix_line_number_list = bug_info[self.key_localization][0][self.key_fix_lines]
        fix_location = bug_info[self.key_localization][0][self.key_fix_loc]
        timeout = str(task_config_info[self.key_timeout])
        failing_test_identifiers_list = bug_info[self.key_failing_test_identifiers]
        passing_test_identifiers_list = bug_info[self.key_passing_test_identifiers]
        subject_name = bug_info[self.key_subject]
        additional_tool_param = task_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
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
        for test_id in failing_test_identifiers_list:
            test_id_list += test_id + " "
        if passing_test_identifiers_list:
            filtered_list = self.filter_tests(
                passing_test_identifiers_list, subject_name, bug_id
            )
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

        if self.is_dump_patches:
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

        self.process_status(status)

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info: Dict[str, str]) -> None:
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
            container.fix_permissions(self.container_id, self.dir_output)
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

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> RepairToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:

            self.stats.patches_stats.non_compilable
            self.stats.patches_stats.plausible
            self.stats.patches_stats.size
            self.stats.patches_stats.enumerations
            self.stats.patches_stats.generated

            self.stats.time_stats.total_validation
            self.stats.time_stats.total_build
            self.stats.time_stats.timestamp_compilation
            self.stats.time_stats.timestamp_validation
            self.stats.time_stats.timestamp_plausible
        """
        self.emit_normal("reading output")

        is_error = False
        is_timeout = False
        count_plausible = 0
        count_enumerations = 0
        search_space = 0
        reported_fail_list: Set[str] = set()
        collect_neg = False

        # count number of patch files
        list_output_dir = self.list_dir(self.dir_output)
        self.stats.patch_stats.generated = len(
            [name for name in list_output_dir if "patch" in name]
        )

        # extract information from output log
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(f"output log file: {self.log_output_path}")

        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self.stats.time_stats.timestamp_start = log_lines[0].rstrip()
            self.stats.time_stats.timestamp_end = log_lines[-1].rstrip()

            for line in log_lines:
                if "selected expressions" in line:
                    search_space = search_space + 1
                elif "considering suspicious expressions" in line:
                    count_enumerations = count_enumerations + 1
                elif "repair test suite: []" in line:
                    is_error = True
                    self.emit_warning("[warning] repair test suite: []")
                elif "validation test suite: []" in line:
                    is_error = True
                    self.emit_warning("[warning] validation test suite: []")
                elif "No negative test exists" in line:
                    is_error = True
                    is_timeout = False
                    self.emit_warning("[warning] No negative test exists")
                elif "no patch generated" in line:
                    is_timeout = False
                    count_plausible = 0
                elif "patches successfully generated" in line:
                    is_timeout = False
                elif "running negative tests" in line:
                    collect_neg = True
                elif "excluding test" in line:
                    removing_test_id = line.split("excluding test ")[-1].split(" ")[0]
                    if removing_test_id in reported_fail_list:
                        reported_fail_list.remove(removing_test_id)
                elif "failed to build" in line and "golden" in line:
                    is_error = True
                    self.emit_error("[error] failed to build golden")
                elif "failed to build" in line and "validation" in line:
                    is_error = True
                    self.emit_error("[error] failed to build validation")
                elif "failed to build" in line and "frontend" in line:
                    is_error = True
                    self.emit_error("[error] failed to build frontend")
                elif collect_neg and "running test" in line:
                    t_id = (
                        line.split("running test ")[-1].split(" ")[0].replace("'", "")
                    )
                    reported_fail_list.add(t_id)
                elif collect_neg and "repair test suite" in line:
                    collect_neg = False

        if is_timeout:
            count_enumerations = count_enumerations - 1

        self.stats.patch_stats.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if self.use_valkyrie else "patches",
                )
            )
        )

        if list(reported_fail_list) != fail_list:
            self.emit_warning("[warning] unexpected failing test-cases reported")
            self.emit_warning("expected fail list: {0}".format(",".join(fail_list)))
            reported_list_str = ",".join(list(reported_fail_list))
            if len(reported_fail_list) > 10:
                reported_list_str = ",".join(list(reported_fail_list)[:10]) + "..."
            self.emit_warning("reported fail list: {0}".format(reported_list_str))
        if is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.size = search_space
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.error_stats.is_error = is_error
        return self.stats

    def filter_tests(
        self, test_id_list: List[str], subject: str, bug_id: str
    ) -> List[str]:
        filtered_list: List[str] = []
        filter_list: List[int] = []
        if str(subject).lower() == "gzip":
            filter_list = []
            if bug_id == "884ef6d16c":
                filter_list.extend([4, 11])

        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return list(map(str, filtered_list))
