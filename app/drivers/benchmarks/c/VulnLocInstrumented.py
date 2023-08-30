import os

from app.drivers.benchmarks.c.VulnLoc import VulnLoc


class VulnLocInstrumented(VulnLoc):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__()
