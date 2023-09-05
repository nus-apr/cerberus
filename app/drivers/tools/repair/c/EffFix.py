import os
from datetime import datetime
from os.path import join
from typing import Any
from typing import Dict

from app.core.utilities import escape_ansi
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool


class EffFix(AbstractRepairTool):
    relative_binary_path = None
    bug_conversion_table = {
        "Memory Leak": "MEMORY_LEAK_C",
        "Null Pointer Dereference": "NULLPTR_DEREFERENCE",
    }

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "rshariffdeen/efffix"
        super().__init__(self.name)

    def rerun_configuration(self, config_script):
        self.emit_normal("re-running configuration")
        f1x_config_path = self.dir_expr + f"/{self.name}-config"
        dir_src = join(self.dir_expr, "src")
        self.write_file(
            [
                "#!/bin/bash\n",
                f"cd {dir_src}\n",
                "make distclean; rm -f CMakeCache.txt\n",
                f"CC=f1x-cc CXX=f1x-cxx {config_script} {self.dir_expr}\n",
            ],
            f1x_config_path,
        )
        reconfig_command = "bash {}".format(f1x_config_path)
        log_reconfig_path = join(self.dir_logs, f"{self.name}-re-config.log")
        self.run_command(reconfig_command, log_file_path=log_reconfig_path)

    def populate_config_file(self, bug_info, config_path, dir_pre):
        config_info: Dict[str, Any] = dict()
        bug_type = bug_info[self.key_bug_type]
        if bug_type not in self.bug_conversion_table:
            self.error_exit(f"Unsupported bug type: {bug_type}")

        if self.key_source not in bug_info:
            self.error_exit(
                f"Missing memory source information in benchmark, required for {self.name}"
            )
        if self.key_sink not in bug_info:
            self.error_exit(
                f"Missing memory sink information in benchmark, required for {self.name}"
            )

        pulse_extra = ""
        subject_name = bug_info[self.key_subject]
        if subject_name == "openssl-1":
            pulse_extra = "--pulse-model-malloc-pattern CRYPTO_malloc --pulse-model-free-pattern CRYPTO_free --pulse-model-realloc-pattern CRYPTO_realloc\n"
        elif subject_name == "openssl-3":
            pulse_extra = "--pulse-model-malloc-pattern CRYPTO_malloc --pulse-model-free-pattern CRYPTO_free --pulse-model-realloc-pattern CRYPTO_realloc --pulse-skip-procedures 'test_single_eval\|openssl_add_all_*'\n"

        compile_list = bug_info.get(self.key_compile_programs, [])
        dir_src = join(self.dir_expr, "src")
        config_info["tag_id"] = bug_info[self.key_bug_id]
        config_info["config_command"] = bug_info[self.key_config_command]
        config_info["build_command"] = bug_info[self.key_build_command]
        config_info["build_command_repair"] = f"make {' '.join(compile_list)}"
        config_info["clean_command"] = "make clean"
        config_info["src_dir"] = dir_src
        config_info["bug_type"] = self.bug_conversion_table[bug_type]
        config_info["bug_file"] = bug_info[self.key_source]["src-file"]
        config_info["bug_procedure"] = bug_info[self.key_source]["procedure"]
        config_info["bug_start_line"] = bug_info[self.key_source]["line"]
        config_info["bug_end_line"] = bug_info[self.key_sink]["line"]
        config_info["runtime_dir_pre"] = dir_pre
        config_info["runtime_dir_repair"] = self.dir_output
        config_info["pulse_extra_command"] = pulse_extra
        content = ""
        for key in config_info:
            content += f"{key}:{config_info[key]}" + " \n"
        self.write_file(content, config_path)

    def prepare(self, bug_info):
        tool_dir = join(self.dir_expr, self.name)
        self.emit_normal(" preparing subject for repair with " + self.name)
        if not self.is_dir(tool_dir):
            self.run_command(f"mkdir -p {tool_dir}", dir_path=self.dir_expr)
        dir_src = join(self.dir_expr, "src")
        clean_command = "rm /tmp/td_candidates/*; make clean"
        self.run_command(clean_command, dir_path=dir_src)
        dir_pre = join(self.dir_expr, "pre")
        if not self.is_dir(dir_pre):
            self.run_command(f"mkdir {dir_pre}")
        config_path = join(self.dir_expr, self.name, "repair.conf")
        self.populate_config_file(bug_info, config_path, dir_pre)
        config_script = bug_info.get(self.key_config_script, None)
        if config_script:
            config_script = join(self.dir_setup, config_script)
            self.rerun_configuration(config_script)
        time = datetime.now()
        compile_list = bug_info.get(self.key_compile_programs, [])
        names_100 = ["swoole", "x264", "p11-kit", "openssl-1"]
        names_50 = ["snort", "openssl-3"]
        subject_name = bug_info[self.key_subject]
        num_disjuncts = 50
        if subject_name in names_100:
            num_disjuncts = 100
        analysis_command = (
            f"effFix --stage pre --disjuncts {num_disjuncts} {config_path}"
        )

        log_analysis_path = join(self.dir_logs, "efffix-pre-output.log")
        self.run_command(
            analysis_command,
            dir_path=dir_src,
            log_file_path=log_analysis_path,
        )

        self.emit_normal(
            " preparation took {} second(s)".format(
                (datetime.now() - time).total_seconds()
            )
        )
        return config_path

    def run_repair(self, bug_info, repair_config_info):
        config_path = self.prepare(bug_info)
        super(EffFix, self).run_repair(bug_info, repair_config_info)
        if self.is_instrument_only:
            return
        task_conf_id = repair_config_info[self.key_id]
        bug_id = str(bug_info[self.key_bug_id])
        timeout_h = str(repair_config_info[self.key_timeout])
        timeout_m = str(int(float(timeout_h) * 60))
        additional_tool_param = repair_config_info[self.key_tool_params]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        dir_src = join(self.dir_expr, "src")
        clean_command = "make clean"
        self.run_command(clean_command, dir_path=dir_src)

        names_100 = ["swoole", "x264", "p11-kit", "openssl-1"]
        names_50 = ["snort", "openssl-3"]
        subject_name = bug_info[self.key_subject]
        num_disjuncts = 50
        if subject_name in names_100:
            num_disjuncts = 100

        budget_str = ""
        if "budget" not in additional_tool_param:
            budget_str = f"--budget {timeout_m}"
        self.timestamp_log_start()
        repair_command = (
            f"timeout -k 5m {timeout_h}h effFix "
            f"--stage repair --disjuncts {num_disjuncts} {budget_str} "
            f"{additional_tool_param} {config_path}"
        )
        status = self.run_command(
            repair_command,
            dir_path=dir_src,
            log_file_path=self.log_output_path,
        )

        self.process_status(status)
        self.emit_highlight("log file: {0}".format(self.log_output_path))
        self.timestamp_log_end()
        clean_command = "rm /tmp/*footpatch*"
        self.run_command(clean_command, dir_path=dir_src)

    def save_artifacts(self, dir_info):
        super(EffFix, self).save_artifacts(dir_info)
        return

    def analyse_output(self, dir_info, bug_id, fail_list):
        json_report = join(self.dir_output, "result.json")
        dir_patch = join(self.dir_output, "final-patches")
        list_patches = self.list_dir(dir_patch, regex="*.patch")
        count_enumerations = 0
        count_plausible = 0
        space_size = 0
        self.stats.patch_stats.generated = len(list_patches)
        is_error = False

        self.emit_normal("reading stdout log")
        if not self.log_output_path or not self.is_file(self.log_output_path):
            self.emit_warning("no output log file found")
            return self.stats

        self.emit_highlight(" Log File: " + self.log_output_path)
        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self.stats.time_stats.timestamp_start = escape_ansi(log_lines[0].strip())
        self.stats.time_stats.timestamp_end = escape_ansi(log_lines[-1].strip())
        if self.is_file(json_report):
            self.emit_normal("reading result.json")
            result_info = self.read_json(json_report, encoding="iso-8859-1")
            space_size = result_info["stats"]["total_search_space"]
            count_enumerations = result_info["stats"]["total_num_patches"]
            count_plausible = result_info["stats"][
                "total_num_locally_plausible_patches"
            ]
        else:
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Adding new patch" in line:
                    count_enumerations += 1
                elif "Plausible Patch:" in line:
                    count_plausible += 1
                elif "search space size: " in line:
                    size_str = escape_ansi(
                        line.split("search space size: ")[-1].strip()
                    )
                    space_size = int(size_str)
            if is_error:
                self.emit_error("[error] error detected in logs")

        self.stats.patch_stats.plausible = count_plausible
        self.stats.patch_stats.enumerations = count_enumerations
        self.stats.patch_stats.size = space_size
        self.stats.error_stats.is_error = is_error
        return self.stats
