import os
from app.drivers.tools.AstorTool import AstorTool


class jGenProg(AstorTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(jGenProg, self).__init__()
        self.mode = "jgenprog"
