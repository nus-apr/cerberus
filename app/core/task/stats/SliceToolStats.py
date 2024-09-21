from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.PatchStats import PatchStats
from app.core.task.stats.ReportStats import ReportStats
from app.core.task.stats.ToolStats import ToolStats


class SliceToolStats(ToolStats):
    patch_stats: PatchStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.patch_stats = PatchStats()
        self.bug_info = {}
        self.config_info = {}
        super(SliceToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(SliceToolStats, self).get_dict()
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
            "{1} count invalid patches: {0}\n".format(
                self.patch_stats.non_compilable, prefix
            )
        )

        printer(
            "{1} count incorrect patches: {0}\n".format(
                self.patch_stats.get_implausible(), prefix
            )
        )

        printer(
            "{1} count plausible patches: {0}\n".format(
                self.patch_stats.plausible, prefix
            )
        )
        super(SliceToolStats, self).write(printer, prefix)
