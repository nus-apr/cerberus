import os
import re
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.drivers.tools.AbstractTool import AbstractTool


class F1X(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(F1X, self).__init__(self.name)
        self.image_name = "rshariffdeen/f1x"

    def generate_test_driver(self):
        test_script_path = self.dir_setup + "/test.sh"
        test_driver_path = self.dir_expr + "/f1x-test"

        self.write_file(
            ["#!/bin/bash\n", "bash {0} /experiment $@".format(test_script_path)],
            test_driver_path,
        )

        perm_command = "chmod +x {}".format(test_driver_path)
        self.run_command(perm_command)

    def repair(self, bug_info, config_info):
        super(F1X, self).repair(bug_info, config_info)
        if values.only_instrument:
            return
        emitter.normal("\t\t\t running repair with " + self.name)
        conf_id = config_info[definitions.KEY_ID]
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        fix_file = bug_info[definitions.KEY_FIX_FILE]
        fix_location = bug_info[definitions.KEY_FIX_LOC]
        passing_test_list = bug_info[definitions.KEY_PASSING_TEST]
        failing_test_list = bug_info[definitions.KEY_FAILING_TEST]
        timeout = str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        subject_name = bug_info[definitions.KEY_SUBJECT]
        benchmark_name = bug_info[definitions.KEY_BENCHMARK]
        additional_tool_param = config_info[definitions.KEY_TOOL_PARAMS]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        self.generate_test_driver()
        test_driver_path = join(self.dir_expr, "f1x-test")
        build_script_path = (
            join(self.dir_setup, "build.sh")
            if not self.is_file(join(self.dir_inst, "build.sh"))
            else join(self.dir_inst, "build.sh")
        )
        test_id_list = ""
        for test_id in failing_test_list:
            test_id_list += test_id + " "
        if passing_test_list:
            filtered_list = self.filter_tests(
                passing_test_list, subject_name, bug_id, benchmark_name
            )
            for test_id in filtered_list:
                test_id_list += test_id + " "

        abs_path_buggy_file = join(
            self.dir_expr, "src", fix_location if fix_location else fix_file
        )
        dir_patch = "output/patches"
        mkdir_command = "mkdir -p " + dir_patch
        self.run_command(mkdir_command, self.log_output_path, "/")

        self.timestamp_log_start()

        repair_command = "timeout -k 5m {}h f1x ".format(str(timeout))
        repair_command += " -f {0} ".format(abs_path_buggy_file)
        repair_command += " -t {0} ".format(test_id_list)
        repair_command += " -T 15000"
        repair_command += " --driver={0} ".format(test_driver_path)
        repair_command += ' -b "{0} /experiment "'.format(build_script_path)
        if values.dump_patches:
            repair_command += " --output-space patch-space "
        if values.debug:
            repair_command += " -v "

        dry_command = repair_command + " --disable-dteq"
        self.run_command(dry_command, self.log_output_path, self.dir_expr)
        all_command = (
            repair_command
            + " --enable-assignment --disable-dteq --enable-validation  -a -o {}  ".format(
                self.dir_output
            )
        )
        if additional_tool_param:
            all_command = all_command + " " + additional_tool_param
        status = self.run_command(all_command, self.log_output_path, self.dir_expr)
        # repair_command = repair_command + "--enable-validation --disable-dteq  -a -o patches-top --output-top 10 -v"
        # status = self.run_command(repair_command, self.log_output_path, dir_expr, container_id)
        if status != 0:
            emitter.warning(
                "\t\t\t(warning) {0} exited with an error code {1}".format(
                    self.name, status
                )
            )
        else:
            emitter.success("\t\t\t(success) {0} ended successfully".format(self.name))
        emitter.highlight("\t\t\tlog file: {0}".format(self.log_output_path))

        if values.dump_patches:
            self.create_patches_from_space(fix_file)
        self.timestamp_log_end()

    def create_patches_from_space(self, source_file):
        script_name = "{}/{}-dump-patches.py".format(self.dir_expr, self.name)
        abs_path_buggy_file = self.dir_expr + "/src/" + source_file
        dump_command = "timeout -k 5m 1h python3 {} {} {}".format(
            script_name, abs_path_buggy_file, self.dir_expr
        )
        self.run_command(dump_command, self.log_output_path, self.dir_expr)

    def filter_tests(self, test_id_list, subject, bug_id, benchmark_name):
        filtered_list = []
        filter_list = []
        if benchmark_name == "manybugs":
            if str(subject).lower() == "python":
                filter_list = [87, 172, 209, 222, 226]
                if bug_id == "69372":
                    filter_list.extend([240, 322, 323, 324])
                elif bug_id == "69935":
                    filter_list.extend([240, 322, 323, 324])
                elif bug_id == "69935":
                    filter_list.extend([240, 322, 323, 324])

            elif str(subject).lower() == "php":
                filter_list = []
                if bug_id == "5bb0a44e06":
                    filter_list.extend([5553, 6548, 9563, 280, 3471])
                elif bug_id == "0927309852":
                    filter_list.extend([7384, 7440, 7551, 7511, 7527, 7639, 9563, 7780])
                elif bug_id == "1e91069eb4":
                    filter_list.extend(
                        [404, 6633, 6777, 7049, 7612, 8695, 8766, 1597, 3908, 6948]
                    )
                elif bug_id == "1f49902999":
                    filter_list.extend(
                        [
                            5553,
                            6110,
                            6472,
                            6475,
                            6478,
                            6485,
                            6489,
                            6494,
                            6501,
                            6503,
                            6507,
                            6853,
                            7165,
                            9563,
                            3471,
                            10638,
                        ]
                    )
                elif bug_id == "b84967d3e2":
                    filter_list.extend([5553, 9563, 3471, 10638])
                elif bug_id == "1d984a7ffd":
                    filter_list.extend([3339, 5553, 9563, 3471, 10638])
                elif bug_id == "6e74d95f34":
                    filter_list.extend([5553, 9563, 3471, 10638, 2298])
                elif bug_id == "8deb11c0c3":
                    filter_list.extend(
                        [404, 6633, 6777, 7049, 7615, 8695, 8766, 1597, 6948]
                    )
                elif bug_id == "2adf58cfcf":
                    filter_list.extend(
                        [3836, 4037, 5553, 5797, 5806, 9563, 280, 3471, 10638]
                    )
                elif bug_id == "3acdca4703":
                    filter_list.extend(
                        [3836, 4037, 5553, 5797, 5806, 9563, 3471, 7527, 10638, 6512]
                    )
                elif bug_id == "5a8c917c37":
                    filter_list.extend(
                        [
                            3836,
                            4037,
                            5553,
                            5797,
                            5806,
                            9563,
                            3471,
                            5137,
                            6336,
                            9617,
                            10638,
                        ]
                    )
                elif bug_id == "2e25ec9eb7":
                    filter_list.extend(
                        [3836, 4037, 5553, 5797, 5806, 9563, 10569, 280, 3471, 10638]
                    )
                elif bug_id == "77ed819430":
                    filter_list.extend(
                        [3836, 4037, 5553, 5797, 5806, 9563, 3471, 10638]
                    )
                elif bug_id == "efcb9a71cd":
                    filter_list.extend(
                        [404, 6633, 6777, 7049, 8695, 8766, 303, 1778, 3908, 6948]
                    )
                elif bug_id == "09b990f499":
                    filter_list.extend(
                        [3836, 4037, 5553, 5797, 5806, 9563, 3471, 7237, 7357, 10638]
                    )
                elif bug_id == "821d7169d9":
                    filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
                elif bug_id == "daecb2c0f4":
                    filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
                elif bug_id == "964f44a280":
                    filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
                elif bug_id == "1056c57fa9":
                    filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471])
                elif bug_id == "05c5c8958e":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 3575, 6219])
                elif bug_id == "d4ae4e79db":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 3575, 6219])
                elif bug_id == "b5f15ef561":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
                elif bug_id == "2e5d5e5ac6":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
                elif bug_id == "9b86852d6e":
                    filter_list.extend(
                        [
                            3940,
                            4144,
                            5912,
                            5921,
                            9787,
                            9834,
                            10578,
                            10976,
                            11133,
                            11135,
                            3575,
                            6219,
                        ]
                    )
                elif bug_id == "c1e510aea8":
                    filter_list.extend([3940, 4144, 5912, 5921, 6648, 9787, 6219, 3575])
                elif bug_id == "fb37f3b20d":
                    filter_list.extend(
                        [3940, 4144, 5912, 5921, 9787, 9834, 3575, 4149, 6219, 6648]
                    )
                elif bug_id == "13ba2da5f6":
                    filter_list.extend(
                        [
                            3940,
                            4144,
                            5912,
                            5921,
                            6028,
                            6061,
                            6072,
                            9787,
                            9834,
                            3442,
                            3575,
                            6219,
                            2238,
                            9787,
                            10578,
                        ]
                    )
                elif bug_id == "3c7a573a2c":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834])
                elif bug_id == "bc810a443d":
                    filter_list.extend(
                        [3940, 4144, 5912, 5921, 9787, 9834, 10160, 11381, 11682, 11713]
                    )
                elif bug_id == "d3b20b4058":
                    filter_list.extend(
                        [3940, 4144, 5912, 5921, 9787, 3575, 6219, 7561, 7642]
                    )
                elif bug_id == "f330c8ab4e":
                    filter_list.extend(
                        [3940, 4144, 5912, 5921, 9787, 3575, 6219, 7561, 7642]
                    )
                elif bug_id == "b548293b99":
                    filter_list.extend([418, 7062, 7333, 8997, 9069, 7232, 9267])
                elif bug_id == "db0888dfc1":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 9834, 3575, 6219])
                elif bug_id == "dfa08dc325":
                    filter_list.extend([3940, 4144, 5912, 5921, 9787, 3442, 3575, 6219])
                elif bug_id == "52c36e60c4":
                    filter_list.extend(
                        [3940, 4144, 5912, 5921, 9787, 9834, 2400, 3390, 3431, 3443]
                    )
                elif bug_id == "acaf9c5227":
                    filter_list.extend(
                        [3958, 4162, 5936, 5945, 9824, 3593, 6245, 6247, 6681]
                    )
                elif bug_id == "6672171672":
                    filter_list.extend([3958, 4162, 5936, 5945, 9824, 9871, 3593, 6245])
                elif bug_id == "34fe62619d":
                    filter_list.extend(
                        [325, 418, 963, 7200, 7471, 9145, 9216, 7370, 9437]
                    )
                elif bug_id == "cdc512afb3":
                    filter_list.extend(
                        [
                            4017,
                            4221,
                            6004,
                            6013,
                            9983,
                            10030,
                            2472,
                            3465,
                            3506,
                            3518,
                            3524,
                        ]
                    )
                elif bug_id == "d4f05fbffc":
                    filter_list.extend([4017, 4221, 6004, 6013, 9983, 3650, 6314])
                elif bug_id == "efc94f3115":
                    filter_list.extend(
                        [
                            4017,
                            4221,
                            6004,
                            6013,
                            9983,
                            10030,
                            3650,
                            5572,
                            6052,
                            6314,
                            5332,
                        ]
                    )
                elif bug_id == "7337a901b7":
                    filter_list.extend([4017, 4221, 6004, 6013, 9983, 3650, 6314])
                elif bug_id == "8d520d6296":
                    filter_list.extend(
                        [
                            8747,
                            10578,
                            10807,
                            10976,
                            11074,
                            11076,
                            11078,
                            11085,
                            11086,
                            11091,
                            11096,
                            11098,
                            11103,
                            11117,
                            11121,
                            11133,
                            11135,
                            11150,
                            11163,
                            6679,
                            8073,
                            8140,
                            9707,
                        ]
                    )
            elif str(subject).lower() == "gmp":
                filter_list = [34]

        for t_id in test_id_list:
            if int(t_id) not in filter_list:
                filtered_list.append(t_id)

        return filtered_list

    def read_log_file(self):
        if self.is_file(self.log_output_path):
            log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
            self._time.timestamp_start = log_lines[0].rstrip()
            self._time.timestamp_end = log_lines[-1].rstrip()
            for line in log_lines:
                if "candidates evaluated: " in line:
                    count = (
                        line.split("candidates evaluated: ")[-1]
                        .strip()
                        .replace("\n", "")
                    )
                    if str(count).isnumeric():
                        self._space.enumerations = int(count)
                elif "validation time: " in line:
                    time = line.split("validation time: ")[-1].strip().replace("\n", "")
                    self._time.total_validation += float(time)
                elif "build time: " in line:
                    time = line.split("build time: ")[-1].strip().replace("\n", "")
                    self._time.total_build += float(time)
                elif "validating patch " in line:
                    self._space.enumerations += 1
                elif "search space size: " in line:
                    self._space.generated = int(line.split("search space size: ")[-1])
                elif "plausible patches: " in line:
                    self._space.plausible = int(line.split("plausible patches: ")[-1])
                elif "failed to infer compile commands" in line:
                    self._space.generated = -1
                elif "explored count: 1" in line:
                    if self._time.timestamp_validation == 0:
                        # self._time.timestamp_validation = (
                        #     line.split("[info]")[0].replace("[", "").replace("]", "")
                        # )
                        pass

                elif "PASS" in line and "[debug]" in line:
                    if self._time.timestamp_plausible == 0:
                        # self._time.timestamp_plausible = (
                        #     line.split("[debug]")[0].replace("[", "").replace("]", "")
                        # )
                        pass

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id)
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
            emitter.warning("\t\t\t(warning) no output log file found")
            return self._space, self._time, self._error

        emitter.highlight("\t\t\t Log File: " + self.log_output_path)

        if self._error.is_error:
            emitter.error("\t\t\t\t(error) error detected in logs")

        self.read_log_file()

        self._space.generated = len(
            self.list_dir(
                join(
                    self.dir_output,
                    "patch-valid" if values.use_valkyrie else "patches",
                )
            )
        )
        if values.use_valkyrie:
            self._space.plausible = self._space.generated

        return self._space, self._time, self._error
