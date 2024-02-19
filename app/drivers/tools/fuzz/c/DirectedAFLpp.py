import os
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.fuzz.c.AbstractAFL import AbstractAFL


class DirectedAFLpp(AbstractAFL):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "wolffdy/joern-directed-aflpp"
        super().__init__()

    def prepare_for_fuzz(self, bug_info):
        bug_info["src"] = {"root_abspath": os.path.join(self.dir_expr, "src")}
        bug_info["test_dir_abspath"] = self.dir_setup
        self.write_json(bug_info, os.path.join(self.dir_expr, "meta-data.json"))

        self.run_command(
            "python3 /opt/selective_instrument.py {}".format(
                os.path.join(self.dir_expr, "meta-data.json")
            ),
            dir_path="/opt/",
        )
