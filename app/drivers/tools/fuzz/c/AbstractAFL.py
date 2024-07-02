import abc
import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class AbstractAFL(AbstractFuzzTool):
    def __init__(self) -> None:
        super().__init__(self.name)

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> FuzzToolStats:
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """
        return self.stats

    @abc.abstractmethod
    def prepare_for_fuzz(self, bug_info: Dict[str, Any]) -> None:
        pass

    @abc.abstractmethod
    def get_params(self, bug_info: Dict[str, Any]) -> str:
        return str(bug_info.get("fuzz_params", ""))

    def invoke(
        self, bug_info: Dict[str, Any], task_config_info: Dict[str, Any]
    ) -> None:

        timeout = int(float(task_config_info[self.key_timeout]) * 60)

        if self.key_bin_path not in bug_info:
            self.error_exit("no binary path provided")

        initial_corpus = join(self.dir_expr, "initial-corpus")

        dictionary = ""
        if self.is_file(join(self.dir_setup, self.name, "autodict.dict")):
            dictionary = "-x {}".format(
                join(self.dir_setup, self.name, "autodict.dict")
            )

        self.run_command("mkdir {}".format(initial_corpus))

        additional_params = (
            task_config_info.get(self.key_tool_params, "")
            + " "
            + self.get_params(bug_info)
        )

        if "-C" in additional_params:
            self.copy_crashing_tests(initial_corpus)
        else:
            self.copy_benign_tests(initial_corpus)

        if (
            self.key_config_script not in bug_info
            or self.key_build_script not in bug_info
        ):
            self.emit_error(
                "AFL++ needs to rebuild the project with coverage instrumntation"
            )
        self.clean_subject(bug_info)
        self.prepare_for_fuzz(bug_info)
        self.timestamp_log_start()
        fuzz_command = "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {timeout}m afl-fuzz -i {input_folder} -o {output_folder} -d -m none {dict} {additional_params} -- {binary} {binary_input}'".format(
            timeout=timeout,
            additional_params=additional_params,
            input_folder=initial_corpus,
            output_folder=self.dir_output,
            dict=dictionary,
            binary=join(self.dir_expr, "src", bug_info[self.key_bin_path]),
            binary_input=bug_info[self.key_crash_cmd].replace("$POC", "@@"),
        )
        self.emit_normal(f"executing fuzz command with {self.name}")
        status = self.run_command(
            fuzz_command,
            self.log_output_path,
            join(self.dir_expr, "src"),
            env={"AFL_NO_UI": str(1), "AFL_CRASHING_SEEDS_AS_NEW_CRASH": str(1)},
        )

        self.process_status(status)

        self.timestamp_log_end()

        self.emit_normal("Genrating meta-data.json")

        base_dir = join(self.dir_output, "default")
        source_crash_dir = join(base_dir, "crashes")
        source_benign_dir = join(base_dir, "queue")

        target_benign_dir = join(self.dir_output, "benign_tests")
        target_crash_dir = join(self.dir_output, "crashing_tests")

        self.run_command("mkdir {}".format(target_benign_dir))
        self.run_command("mkdir {}".format(target_crash_dir))

        if "-C" not in additional_params:
            # Crash exploration will be more focused on generating crashing tests but we cannot be sure
            self.copy_benign_tests(target_benign_dir)
        self.copy_crashing_tests(target_crash_dir)

        self.run_command(
            "bash -c 'cp -r {}/id* {} '".format(source_benign_dir, target_benign_dir)
        )
        self.run_command(
            "bash -c 'cp -r {}/id* {} '".format(source_crash_dir, target_crash_dir)
        )

        new_bug_info: Dict[str, Any] = {
            self.key_generator: self.name,
            self.key_exploit_inputs: [{"format": "raw", "dir": "crashing_tests"}],
            self.key_benign_inputs: [{"format": "raw", "dir": "benign_tests"}],
            "test_dir_abspath": self.dir_setup,
        }
        self.write_json(
            [{self.key_analysis_output: [new_bug_info]}],
            join(self.dir_output, "meta-data.json"),
        )

    def copy_crashing_tests(self, corpus_path: str) -> None:
        # Get Crashing tests
        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, "crashing_tests"),
                corpus_path,
            )
        )

        # Get custom seeds
        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, self.name, "initial-crashing-corpus"),
                corpus_path,
            )
        )

    def copy_benign_tests(self, corpus_path: str) -> None:
        # Get Benign Tests
        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, "benign_tests"),
                corpus_path,
            )
        )

        # Get special seeds
        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, self.name, "initial-benign-corpus"),
                corpus_path,
            )
        )

        # Ensure at least one test-case
        corpus = self.list_dir(corpus_path)
        if len(corpus) == 0 or corpus == [corpus_path]:
            self.write_file(["hi"], join(corpus_path, "hi.txt"))
