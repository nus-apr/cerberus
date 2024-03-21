from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.ToolStats import ToolStats


class CompositeStats:
    def get_dict(self) -> Dict[str, Any]:
        summary: Dict[str, Any] = {}
        return summary


class CompositeToolStats(ToolStats):
    composite_stats: CompositeStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.composite_stats = CompositeStats()
        super(CompositeToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(CompositeToolStats, self).get_dict()
        res["details"]["composite_stats"] = self.composite_stats.get_dict()
        return res

    def write(self, printer: Callable[[str], Any], prefix: str = "") -> None:
        # printer("{1} executions: {0}\n".format(self.fuzzing_stats.executions, prefix))
        super(CompositeToolStats, self).write(printer, prefix)
