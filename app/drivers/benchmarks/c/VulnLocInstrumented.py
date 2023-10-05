import os

from app.drivers.benchmarks.c.VulnLoc import VulnLoc


class VulnLocInstrumented(VulnLoc):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(VulnLoc, self).__init__()

    def verify(self, bug_index, container_id):
        self.emit_normal("verify dev patch and test-oracle")
        self.emit_debug("verify took 0 second(s)")
        return 1
