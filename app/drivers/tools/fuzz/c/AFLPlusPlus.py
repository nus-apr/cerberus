import os
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core.task.stats.FuzzToolStats import FuzzToolStats
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.fuzz.c.AbstractAFL import AbstractAFL


class AFLPlusPlus(AbstractAFL):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "mirchevmp/aflplusplus"
        super().__init__()

    def prepare_for_fuzz(self, bug_info: Dict[str, Any]) -> None:
        self.run_command(
            "bash -c ' CC=afl-clang-fast CXX=afl-clang-fast++ {}'".format(
                join(self.dir_setup, bug_info[self.key_config_script])
            )
        )
        self.run_command(
            "bash -c ' CC=afl-clang-fast CXX=afl-clang-fast++ {}'".format(
                join(self.dir_setup, bug_info[self.key_build_script])
            )
        )

    def analyse_output(
        self, dir_info: DirectoryInfo, bug_id: str, fail_list: List[str]
    ) -> FuzzToolStats:
        dir_test_benign = join(self.dir_output, "benign_tests")
        dir_test_crash = join(self.dir_output, "crashing_tests")

        crashing_test_list = self.list_dir(dir_test_crash)
        non_crashing_test_lsit = self.list_dir(dir_test_benign)

        self.stats.fuzzing_stats.count_benign_tests = len(non_crashing_test_lsit)
        self.stats.fuzzing_stats.count_crash_tests = len(crashing_test_list)

        return self.stats
