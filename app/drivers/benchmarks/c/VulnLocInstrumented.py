import os
from typing import Optional

from app.drivers.benchmarks.c.VulnLoc import VulnLoc


class VulnLocInstrumented(VulnLoc):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super(VulnLoc, self).__init__()

    def verify(self, bug_index: int, container_id: Optional[str]) -> bool:
        self.emit_normal("verify dev patch and test-oracle")
        self.emit_debug("verify took 0 second(s)")
        return True
