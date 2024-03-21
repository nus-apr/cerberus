from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.ToolStats import ToolStats


class SelectionStats:
    size: int = -1
    enumerations: int = -1
    selected: int = -1
    duplicates: int = -1

    def get_exploration_ratio(self) -> float:
        return (self.enumerations / self.size) * 100

    def get_dict(self) -> Dict[str, int]:
        summary = {
            "search space": self.size,
            "enumerations": self.enumerations,
            "selected": self.selected,
            "duplicates": self.duplicates,
        }
        return summary


class SelectToolStats(ToolStats):
    patch_stats: SelectionStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.patch_stats = SelectionStats()
        self.bug_info = {}
        self.config_info = {}
        super(SelectToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(SelectToolStats, self).get_dict()
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
            "{1} count duplications: {0}\n".format(self.patch_stats.duplicates, prefix)
        )
        printer("{1} count selections: {0}\n".format(self.patch_stats.selected, prefix))

        super(SelectToolStats, self).write(printer, prefix)
