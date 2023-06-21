from app.core.ToolNamesEnum import ToolNamesEnum
from app.drivers.tools.repair.java.Nopol import Nopol


class ToolLoader:

    @staticmethod
    def load_tool(tool_name: str):

        if tool_name == ToolNamesEnum.NOPOL.value:
            return Nopol()
        else:
            raise ValueError("No such tool")
