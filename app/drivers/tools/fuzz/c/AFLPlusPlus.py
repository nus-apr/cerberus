import os
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.fuzz.c.AbstractAFL import AbstractAFL


class AFLPlusPlus(AbstractAFL):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "mirchevmp/aflplusplus"
        super().__init__()

    def prepare_for_fuzz(self, bug_info):
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
