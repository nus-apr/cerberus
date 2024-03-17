from datetime import datetime
from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.PatchStats import PatchStats
from app.core.task.stats.ToolStats import ToolStats


class AnalysisToolStats(ToolStats):
    patch_stats: PatchStats

    def __init__(self) -> None:
        self.patch_stats = PatchStats()
        super(AnalysisToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(AnalysisToolStats, self).get_dict()
        res["details"]["space"] = self.patch_stats.get_dict()
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
        super(AnalysisToolStats, self).write(printer, prefix)
