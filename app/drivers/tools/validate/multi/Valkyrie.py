import os
import re
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import values
from app.core.task.stats.ValidateToolStats import ValidateToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.validate.AbstractValidateTool import AbstractValidateTool


class Valkyrie(AbstractValidateTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "rshariffdeen/valkyrie"
        self.path_to_binaries = ["/opt/valkyrie/bin/"]
        self.portable_dirs = ["/opt/valkyrie"]
        self.config_path = ""

    def locate(self) -> None:
        self.tool_folder = (
            join(values.dir_main, "valkyrie")
            if self.locally_running
            else "/opt/valkyrie/"
        )
        if not self.is_dir(self.tool_folder):
            self.error_exit(
                f"Tool directory for {self.name} is not found at {self.tool_folder}"
            )

    def populate_config_file(self, bug_info: Dict[str, Any]) -> str:
        self.emit_normal("generating config file")
        self.config_path = join(self.dir_expr, f"{self.name}.config")
        conf_content = list()
        dir_src = f"{self.dir_expr}/src"
        conf_content.append(f"source_dir:{dir_src}\n")
        if bug_info.get(self.key_language, "").lower() in ["c"]:
            config_script = bug_info[self.key_config_script]
            abs_path_c_script = f"{self.dir_setup}/{config_script}"
            conf_content.append(f"config_script:{abs_path_c_script}\n")

        # if bug_info.get(self.key_localization, None):
        #     localization = bug_info[self.key_localization]
        #     if len(localization) > 1:
        #         self.emit_warning("Multiple localization not supported")
        #     else:
        #         conf_content.append(
        #             f"source_file:{localization[0][self.key_fix_file]}\n"
        #         )
        conf_content.append(f"patch_dir:{self.dir_setup}/patches\n")
        conf_content.append(
            f"test_oracle:{self.dir_setup}/{bug_info[self.key_test_script]}\n"
        )
        conf_content.append(
            f"test_id_list:{','.join(bug_info[self.key_failing_test_identifiers])}\n"
        )
        build_script = bug_info[self.key_build_script]
        abs_path_b_script = f"{self.dir_setup}/{build_script}"
        if build_script:
            conf_content.append(f"build_script:{abs_path_b_script}\n")
        else:
            conf_content.append(f'build_script:-c "exit 0"\n')

        public_test_script = bug_info.get(self.key_pub_test_script)
        if public_test_script:
            conf_content.append(
                f"pub_test_script:{self.dir_setup}/{public_test_script}\n"
            )
        else:
            conf_content.append(
                f"pub_test_script:{self.dir_setup}/{bug_info[self.key_test_script]}\n"
            )
        if bug_info.get(self.key_pvt_test_script, None):
            pvt_script = f"{self.dir_setup}/{bug_info[self.key_pvt_test_script]}"
            conf_content.append(f"pvt_test_script:{pvt_script}\n")
        if bug_info.get(self.key_adv_test_script, None):
            adv_script = f"{self.dir_setup}/{bug_info[self.key_adv_test_script]}"
            conf_content.append(f"adv_test_script:{adv_script}\n")
        conf_content.append(f"output_dir:{self.dir_output}\n")
        conf_content.append("patch_mode:compile\n")
        conf_content.append("patch_per_dir_limit:100\n")
        conf_content.append("reset_command:git reset --hard HEAD\n")
        self.write_file(conf_content, self.config_path)
        return self.config_path

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:
        conf_path = self.populate_config_file(bug_info)
        self.tool_folder = (
            join(values.dir_main, "valkyrie")
            if self.locally_running
            else "/opt/valkyrie/"
        )
        # delete previously validated patches
        self.delete_validated_patches(bug_info)
        task_conf_id = str(self.current_task_profile_id.get("NA"))
        bug_id = str(bug_info[self.key_bug_id])
        timeout = str(task_config_info[self.key_timeout])
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(task_conf_id, self.name.lower(), bug_id),
        )

        timeout_m = str(float(timeout) * 60)
        additional_tool_param = task_config_info[self.key_tool_params]
        self.timestamp_log_start()
        validate_command = (
            "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {0}h valkyrie --conf=".format(
                timeout
            )
            + conf_path
            + " --only-validate "
            + additional_tool_param
            + "'"
        )

        status = self.run_command(
            validate_command, self.log_output_path, self.tool_folder
        )
        self.process_status(status)
        # transform the patch paths
        # self.transform_patches(bug_info)
        self.create_meta_data()
        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def delete_validated_patches(self, bug_info: Dict[str, Any]) -> None:
        if not "validation_output" in bug_info:
            return
        validation_info = bug_info["validation_output"][0]["validation_result"]
        input_patches_dir = f"{self.dir_setup}/patches"
        for _id, _result in validation_info:
            generator, patch_id = _id.split(":")
            patch_file = join(input_patches_dir, generator, patch_id)
            if os.path.isfile(patch_file):
                self.run_command(f"rm -f {patch_file}")

    def create_meta_data(self) -> None:
        result_json_file = f"{self.dir_output}/result.json"
        if self.is_file(result_json_file):
            result_json = self.read_json(result_json_file)
            new_metadata = {"generator": self.name, "validation_result": result_json}

            self.write_json(
                [{"validation_output": [new_metadata]}],
                join(self.dir_output, "meta-data.json"),
            )

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def transform_patches(self, bug_info: Dict[str, Any]) -> None:
        input_patches_dir = f"{self.dir_setup}/patches"
        cp_source_list = [x["name"] for x in bug_info["cp_sources"]]
        patch_list = [
            x for x in self.list_dir(input_patches_dir) if ".patch" in x or ".diff" in x
        ]
        for _p in patch_list:
            with open(_p, "r") as file:
                filedata = file.read()
                dir_src = f"{self.dir_expr}/src"
                for _cp_src in cp_source_list:
                    abs_path = f"{dir_src}/{_cp_src}".replace("//", "/")
                    rel_path = f"/src/{_cp_src}".replace("//", "/")
                    filedata = filedata.replace(abs_path, "").replace(rel_path, "")
            with open(_p, "w") as file:
                file.write(filedata)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> ValidateToolStats:
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
        is_timeout = True
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            for line in log_lines:
                if "Runtime Error" in line:
                    self.stats.error_stats.is_error = True
                elif "statistics" in line:
                    is_timeout = False

        input_patches_dir = f"{self.dir_setup}/patches"
        patch_list = [
            x for x in self.list_dir(input_patches_dir) if ".patch" in x or ".diff" in x
        ]
        self.stats.patch_stats.size = len(patch_list)

        result_json_file = f"{self.dir_output}/result.json"
        result_json = self.read_json(result_json_file)
        if not isinstance(result_json, List):
            result_json = []

        self.stats.patch_stats.enumerations = len(result_json)
        malformed_count = 0
        build_fail_count = 0
        incorrect_count = 0
        fix_fail_count = 0
        plausible_count = 0
        correct_count = 0
        for result in iter(result_json):
            p_file, p_class = result
            if "pass public" in p_class:
                plausible_count += 1
            elif "invalid patch" in p_class:
                malformed_count += 1
            elif "cannot build" in p_class:
                build_fail_count += 1
            elif "incorrect patch" in p_class:
                incorrect_count += 1
            elif "fixed failing" in p_class:
                fix_fail_count += 1
            elif "pass private" in p_class:
                correct_count += 1

        self.stats.patch_stats.plausible = plausible_count
        self.stats.patch_stats.correct = correct_count
        self.stats.patch_stats.non_compilable = build_fail_count
        self.stats.patch_stats.malformed = malformed_count
        self.stats.patch_stats.fix_fail = fix_fail_count
        self.stats.patch_stats.incorrect = incorrect_count

        if self.stats.error_stats.is_error:
            self.emit_error("[error] error detected in logs")
        if is_timeout:
            self.emit_warning("[warning] timeout before ending")
        return self.stats
