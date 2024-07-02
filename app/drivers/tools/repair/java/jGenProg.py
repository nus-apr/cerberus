import os

from app.drivers.tools.repair.java.AstorTool import AstorTool


class jGenProg(AstorTool):
    def __init__(self) -> None:
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__()
        self.mode = "jgenprog"
