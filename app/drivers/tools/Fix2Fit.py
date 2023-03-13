import os
import re
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.drivers.tools.AbstractTool import AbstractTool


class Fix2Fit(AbstractTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Fix2Fit, self).__init__(self.name)
        self.image_name = "rshariffdeen/fix2fit"

    def repair(self, bug_info, config_info):
        super(Fix2Fit, self).repair(bug_info, config_info)
        if values.only_instrument:
            return
        conf_id = str(values.current_profile_id)
        bug_id = str(bug_info[definitions.KEY_BUG_ID])
        fix_location = bug_info[definitions.KEY_FIX_FILE]
        self.log_output_path = join(
            self.dir_logs,
            "{}-{}-{}-output.log".format(conf_id, self.name.lower(), bug_id),
        )
        abs_path_binary = join(
            self.dir_expr, "src", bug_info[definitions.KEY_BINARY_PATH]
        )
        test_id_list = " ".join(bug_info[definitions.KEY_FAILING_TEST]) + " "
        if bug_info[definitions.KEY_PASSING_TEST]:
            filtered_list = self.filter_tests(
                bug_info[definitions.KEY_PASSING_TEST],
                bug_info[definitions.ARG_SUBJECT_NAME],
                bug_id,
            )
            for test_id in filtered_list:
                test_id_list += test_id + " "

        abs_path_buggy_file = join(
            self.dir_expr,
            "src",
            fix_location
            if fix_location
            else self.read_file(self.dir_expr + "/manifest.txt")[0],
        )

        self.timestamp_log_start()
        environment_vars = {
            "SUBJECT_DIR": self.dir_setup,
            "AFL_NO_AFFINITY": "",
            "BUGGY_FILE": abs_path_buggy_file,
            "TESTCASE": test_id_list,
            "CONFIG": "{}/fix2fit/config-driver".format(self.dir_setup),
            "BUILD": "{}/fix2fit/build-driver".format(self.dir_setup),
            "DRIVER": "{}/fix2fit/test-driver".format(self.dir_setup),
            "BINARY": abs_path_binary,
            "T_TIMEOUT": "{}000".format(
                config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE]
            ),
            "TIMEOUT": "{}h; ".format(config_info[definitions.KEY_CONFIG_TIMEOUT]),
            "BINARY_INPUT": bug_info[definitions.KEY_CRASH_CMD],
        }
        # repair_command = "bash -c 'export SUBJECT_DIR={}; ".format(self.dir_setup)
        # repair_command += "export AFL_NO_AFFINITY='';"
        # repair_command += "export BUGGY_FILE={}; ".format(abs_path_buggy_file)
        # repair_command += 'export TESTCASE="{}"; '.format(test_id_list)
        # repair_command += "export CONFIG={}/fix2fit/config-driver; ".format(self.dir_setup)
        # repair_command += "export BUILD={}/fix2fit/build-driver; ".format(self.dir_setup)
        # repair_command += "export DRIVER={}/fix2fit/test-driver; ".format(self.dir_setup)
        # repair_command += "export BINARY={}; ".format(abs_path_binary)
        # repair_command += "export T_TIMEOUT={}000; ".format(config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE])
        # repair_command += "export TIMEOUT={}h; ".format(config_info[definitions.KEY_CONFIG_TIMEOUT])
        # repair_command += 'export BINARY_INPUT="{}"; '.format(bug_info[definitions.KEY_CRASH_CMD])
        repair_command = "timeout -k 5m {}h bash /src/scripts/run.sh ".format(
            str(config_info[definitions.KEY_CONFIG_TIMEOUT])
        )
        repair_command += " >> {0} 2>&1 ".format(self.log_output_path)
        status = self.run_command(
            repair_command, self.log_output_path, self.dir_setup, env=environment_vars
        )
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
        return

    def save_artifacts(self, dir_info):
        dir_patch = join(self.dir_setup, "patches")
        self.run_command("mkdir /output")
        self.run_command("cp -rf {} {}/patches".format(dir_patch, self.dir_output))
        super(Fix2Fit, self).save_artifacts(dir_info)
        return

    def filter_tests(self, test_id_list, subject, bug_id):
        filtered_list = []
        filter_list = []
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
                    [3836, 4037, 5553, 5797, 5806, 9563, 3471, 5137, 6336, 9617, 10638]
                )
            elif bug_id == "2e25ec9eb7":
                filter_list.extend(
                    [3836, 4037, 5553, 5797, 5806, 9563, 10569, 280, 3471, 10638]
                )
            elif bug_id == "77ed819430":
                filter_list.extend([3836, 4037, 5553, 5797, 5806, 9563, 3471, 10638])
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
                filter_list.extend([325, 418, 963, 7200, 7471, 9145, 9216, 7370, 9437])
            elif bug_id == "cdc512afb3":
                filter_list.extend(
                    [4017, 4221, 6004, 6013, 9983, 10030, 2472, 3465, 3506, 3518, 3524]
                )
            elif bug_id == "d4f05fbffc":
                filter_list.extend([4017, 4221, 6004, 6013, 9983, 3650, 6314])
            elif bug_id == "efc94f3115":
                filter_list.extend(
                    [4017, 4221, 6004, 6013, 9983, 10030, 3650, 5572, 6052, 6314, 5332]
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

    def analyse_output(self, dir_info, bug_id, fail_list):
        emitter.normal("\t\t\t analysing output of " + self.name)
        dir_results = join(self.dir_expr, "result")
        conf_id = str(values.current_profile_id)
        self.log_analysis_path = join(
            self.dir_logs,
            "{}-{}-{}-analysis.log".format(conf_id, self.name.lower(), bug_id),
        )
        count_filtered = 0

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

        is_timeout = True
        reported_failing_test = []
        if self.is_file(dir_results + "/original.txt"):
            log_lines = self.read_file(dir_results + "/original.txt")
            self._time.timestamp_start = log_lines[0].replace("\n", "")
            self._time.timestamp_end = log_lines[-1].replace("\n", "")
            for line in log_lines:
                if "no patch found" in line:
                    emitter.warning("\t\t\t\t(warning) no patch found by F1X")
                elif "negative tests: [" in line:
                    reported_failing_test = (
                        str(line)
                        .split("negative tests: [")[-1]
                        .split("]")[0]
                        .split(", ")
                    )
                elif "search space size: " in line:
                    self._space.size = int(
                        line.split("search space size: ")[-1].strip()
                    )

        log_lines = self.read_file(self.log_output_path, encoding="iso-8859-1")
        self._time.timestamp_start = log_lines[0].replace("\n", "")
        self._time.timestamp_end = log_lines[-1].replace("\n", "")
        for line in log_lines:
            if "search space size: " in line:
                self._space.size = int(line.split("search space size: ")[-1].strip())
            elif "candidates evaluated: " in line:
                self._space.enumerations = int(
                    line.split("candidates evaluated: ")[-1].strip()
                )
            elif "exploration progress: " in line:
                self._space.enumerations = (
                    int(
                        line.split("exploration progress: ")[-1]
                        .strip()
                        .replace("%", "")
                    )
                    / 100
                    * self._space.size
                )
            elif "plausible patches: " in line:
                self._space.plausible = int(
                    line.split("plausible patches: ")[-1].strip()
                )
            elif "partition size: " in line:
                self._space.plausible = (
                    int(line.split("partition size: ")[-1].strip())
                    + self._space.plausible
                )
            elif "patches successfully generated" in line:
                is_timeout = False
            elif "no patch found" in line:
                is_timeout = False
            elif "Fail to execute f1x" in line:
                self._error.is_error = True
            elif "tests are not specified" in line:
                self._error.is_error = True
                emitter.warning("\t\t\t\t(warning) no tests provided")
            elif "no negative tests" in line:
                emitter.warning("\t\t\t\t(warning) no negative tests")
            elif "failed to infer compile commands" in line:
                self._error.is_error = True
                emitter.error("\t\t\t\t(error) compilation command not found")
            elif "At-risk data found" in line:
                self._error.is_error = True
                emitter.error("\t\t\t\t(error) previous results have corrupted")

        if self._error.is_error:
            emitter.error("\t\t\t\t(error) error detected in logs")
        if is_timeout:
            emitter.warning("\t\t\t\t(warning) timeout detected")
        if (
            reported_failing_test != fail_list
            and reported_failing_test
            and not is_timeout
        ):
            emitter.warning("\t\t\t\t(warning) unexpected failing test-cases reported")
            emitter.warning(
                "\t\t\t\texpected fail list: {0}".format(",".join(fail_list))
            )
            emitter.warning(
                "\t\t\t\treported fail list: {0}".format(
                    ",".join(reported_failing_test)
                )
            )

        dir_patch = self.dir_setup + "/patches"
        self._space.generated = len(self.list_dir(dir_patch))
        return self._space, self._time, self._error
