from datetime import datetime
from typing import Any
from typing import Dict

from app.core import emitter
from app.core import values
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskStatus import TaskStatus


class FixLocStats:
    size: int = -1
    enumerations: int = -1
    plausible: int = -1
    generated: int = -1
    correct: int = -1

    def get_exploration_ratio(self):
        return (self.enumerations / self.size) * 100

    def get_dict(self, is_validate=False):
        summary = {
            "search space": self.size,
            "enumerations": self.enumerations,
            "plausible": self.plausible,
            "correct": self.correct,
            "generated": self.generated,
        }
        return summary


class LocalizeToolStats(ToolStats):
    fix_loc_stats: FixLocStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self):
        self.fix_loc_stats = FixLocStats()
        self.bug_info = {}
        self.config_info = {}
        super(LocalizeToolStats, self).__init__()

    def get_dict(self):
        res = super(LocalizeToolStats, self).get_dict()
        res["details"]["space"] = self.fix_loc_stats.get_dict()
        if "info" not in res:
            res["info"] = dict()
        res["info"]["bug-info"] = self.bug_info
        res["info"]["config-info"] = self.config_info
        return res

    def write(self, printer, prefix=""):
        printer("{1} search space size: {0}\n".format(self.fix_loc_stats.size, prefix))
        printer(
            "{1} count enumerations: {0}\n".format(
                self.fix_loc_stats.enumerations, prefix
            )
        )

        printer(
            "{1} count plausible locations: {0}\n".format(
                self.fix_loc_stats.plausible, prefix
            )
        )
        printer(
            "{1} count generated locations: {0}\n".format(
                self.fix_loc_stats.generated, prefix
            )
        )

        super(LocalizeToolStats, self).write(printer, prefix)
