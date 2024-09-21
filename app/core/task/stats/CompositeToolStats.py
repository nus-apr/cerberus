from typing import Any
from typing import Callable
from typing import Dict
from typing import List
from typing import Tuple

from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus


class CompositeStats:
    job_statuses: Dict[str, Tuple[int, TaskStatus]]
    test_distribution: Dict[str, Tuple[int, int]]
    tool_stats: Dict[str, ToolStats]
    paths: List[List[str]]
    aggregations: Dict[str, List[ToolStats]]

    def __init__(self) -> None:
        self.job_statuses = {}
        self.test_distribution = {}
        self.tool_stats = {}
        self.paths = []
        self.aggregations = {}

    def get_dict(self) -> Dict[str, Any]:
        summary: Dict[str, Any] = {}
        for key, (value, status) in self.job_statuses.items():
            summary[key] = {
                "value": value,
                "status": str(status),
                "summary": (
                    self.tool_stats[key].get_dict() if key in self.tool_stats else {}
                ),
                "benign_tests": self.test_distribution.get(key, (-1, -1))[0],
                "exploit_inputs": self.test_distribution.get(key, (-1, -1))[1],
            }
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
