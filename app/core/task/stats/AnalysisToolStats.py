from datetime import datetime
from typing import Any
from typing import Callable
from typing import Dict

from app.core.task.stats.ReportStats import ReportStats
from app.core.task.stats.ToolStats import ToolStats


class AnalysisToolStats(ToolStats):
    report_stats: ReportStats

    def __init__(self) -> None:
        self.report_stats = ReportStats()
        super(AnalysisToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(AnalysisToolStats, self).get_dict()
        res["details"]["space"] = self.report_stats.get_dict()
        return res

    def write(self, printer: Callable[[str], Any], prefix: str = "") -> None:
        printer(
            "{1} report(s) generated: {0}\n".format(self.report_stats.generated, prefix)
        )
        super(AnalysisToolStats, self).write(printer, prefix)
