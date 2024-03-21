import os
from os.path import join
from typing import Any
from typing import Dict

from app.drivers.tools.fuzz.c.AbstractAFL import AbstractAFL


class DirectedAFLpp(AbstractAFL):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        self.image_name = "wolffdy/joern-directed-aflpp"
        super().__init__()

    def prepare_for_fuzz(self, bug_info: Dict[str, Any]) -> None:
        metadata_loc = os.path.join(self.dir_expr, "meta-data.json")
        bug_info["src"] = {"root_abspath": os.path.join(self.dir_expr, "src")}
        bug_info["test_dir_abspath"] = self.dir_setup
        bug_info["setup_dir_abspath"] = self.dir_setup
        self.write_json(bug_info, metadata_loc)

        self.run_command(
            "python3 /opt/selective_instrument.py {}".format(metadata_loc),
            dir_path="/opt/",
        )
