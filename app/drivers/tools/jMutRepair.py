import os
from app.drivers.tools.AstorTool import AstorTool


class jMutRepair(AstorTool):

    def __init__(self):
        super(jMutRepair, self).__init__(self.name)
        self.name = os.path.basename(__file__)[:-3].lower()
        self.mode = "jMutRepair"