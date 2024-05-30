from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.PatchStats import PatchStats
from app.core.task.stats.ToolStats import ToolStats


class ValidateToolStats(ToolStats):
    patch_stats: PatchStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.patch_stats = PatchStats()
        self.bug_info = {}
        self.config_info = {}
        super(ValidateToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(ValidateToolStats, self).get_dict()
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
            "{1} count malformed patches: {0}\n".format(
                self.patch_stats.malformed, prefix
            )
        )

        printer(
            "{1} count build failures: {0}\n".format(
                self.patch_stats.non_compilable, prefix
            )
        )

        printer(
            "{1} count fix failed patches: {0}\n".format(
                self.patch_stats.fix_fail, prefix
            )
        )

        printer(
            "{1} count incorrect patches: {0}\n".format(
                self.patch_stats.incorrect, prefix
            )
        )

        printer(
            "{1} count plausible patches: {0}\n".format(
                self.patch_stats.plausible, prefix
            )
        )

        super(ValidateToolStats, self).write(printer, prefix)
