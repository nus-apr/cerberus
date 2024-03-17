from datetime import datetime
from typing import Any
from typing import Callable
from typing import Dict

from app.core import emitter
from app.core import values
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus


class FixLocStats:
    fix_locs: int = -1
    source_files: int = -1
    fix_funcs: int = -1

    def get_dict(self, is_validate: bool = False) -> Dict[str, int]:
        summary = {
            "fix locations": self.fix_locs,
            "source files": self.source_files,
            "fix_functions": self.fix_funcs,
        }
        return summary


class LocalizeToolStats(ToolStats):
    fix_loc_stats: FixLocStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.fix_loc_stats = FixLocStats()
        self.bug_info = {}
        self.config_info = {}
        super(LocalizeToolStats, self).__init__()

    def get_dict(self) -> Dict[str, Any]:
        res = super(LocalizeToolStats, self).get_dict()
        res["details"]["localization"] = self.fix_loc_stats.get_dict()
        if "info" not in res:
            res["info"] = dict()
        res["info"]["bug-info"] = self.bug_info
        res["info"]["config-info"] = self.config_info
        return res

    def write(self, printer: Callable[[str], Any], prefix: str = "") -> None:
        printer(
            "{1} count fix locations: {0}\n".format(self.fix_loc_stats.fix_locs, prefix)
        )

        printer(
            "{1} count unique source files: {0}\n".format(
                self.fix_loc_stats.source_files, prefix
            )
        )
        printer(
            "{1} count fix functions: {0}\n".format(
                self.fix_loc_stats.fix_funcs, prefix
            )
        )

        super(LocalizeToolStats, self).write(printer, prefix)
