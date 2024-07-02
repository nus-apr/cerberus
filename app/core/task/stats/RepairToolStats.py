from datetime import datetime
from typing import Any
from typing import Callable
from typing import Dict

from app.core import emitter
from app.core import values
from app.core.task.stats.PatchStats import PatchStats
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus


class RepairToolStats(ToolStats):
    patch_stats: PatchStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.patch_stats = PatchStats()
        self.bug_info = {}
        self.config_info = {}
        super(RepairToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(RepairToolStats, self).get_dict()
        res["details"]["space"] = self.patch_stats.get_dict()
        if "info" not in res:
            res["info"] = dict()
        res["info"]["bug-info"] = self.bug_info
        res["info"]["config-info"] = self.config_info
        return res

    def write(self, printer: Callable[[str], Any], prefix: str = "") -> None:
        printer("{1} search space size: {0}\n".format(self.patch_stats.size, prefix))
        printer(
            "{1} count enumerations: {0}\n".format(
                self.patch_stats.enumerations, prefix
            )
        )
        printer(
            "{1} count plausible patches: {0}\n".format(
                self.patch_stats.plausible, prefix
            )
        )
        printer("{1} count generated: {0}\n".format(self.patch_stats.generated, prefix))
        printer(
            "{1} count non-compiling patches: {0}\n".format(
                self.patch_stats.non_compilable, prefix
            )
        )
        printer(
            "{1} count implausible patches: {0}\n".format(
                self.patch_stats.get_implausible(), prefix
            )
        )
        super(RepairToolStats, self).write(printer, prefix)
