import os

from app.drivers.tools.repair.java.AstorTool import AstorTool


class Cardumen(AstorTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.mode = "cardumen"
