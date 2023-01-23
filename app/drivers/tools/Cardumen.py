import os
from os.path import join
import re
from app.core import definitions, emitter, values
from app.core import utilities
from app.drivers.tools.AstorTool import AstorTool


class Cardumen(AstorTool):
    def __init__(self):
        super(Cardumen, self).__init__(self.name)
        self.name = os.path.basename(__file__)[:-3].lower()
        self.mode = "cardumen"
