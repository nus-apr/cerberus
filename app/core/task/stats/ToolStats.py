from datetime import datetime
from typing import Any
from typing import Callable
from typing import Dict

from app.core import emitter
from app.core import values
from app.core.task.stats.ContainerStats import ContainerStats
from app.core.task.stats.ErrorStats import ErrorStats
from app.core.task.stats.TimeStats import TimeStats
from app.core.task.TaskStatus import TaskStatus


class ToolStats:
    time_stats: TimeStats
    container_stats: ContainerStats
    error_stats: ErrorStats
    bug_info: Dict[str, Any]
    config_info: Dict[str, Any]

    def __init__(self) -> None:
        self.time_stats = TimeStats()
        self.container_stats = ContainerStats()
        self.error_stats = ErrorStats()

    def reset(self) -> None:
        self.time_stats = TimeStats()
        self.container_stats = ContainerStats()
        self.error_stats = ErrorStats()

    def get_dict(self) -> Dict[str, Any]:
        return {
            "status": str(values.experiment_status.get(TaskStatus.NONE)),
            "details": {
                "time": self.time_stats.get_dict(),
                "container": self.container_stats.get_dict(),
            },
        }

    def write(self, printer: Callable[[str], Any], prefix: str = "") -> None:
        # printer(
        #     "{1} time build: {0} seconds\n".format(self.time_stats.total_build, prefix)
        # )
        # printer(
        #     "{1} time validation: {0} seconds\n".format(
        #         self.time_stats.total_validation, prefix
        #     )
        # )
        printer(
            "{1} time duration: {0} seconds\n".format(
                self.time_stats.get_duration(), prefix
            )
        )

        # if values.use_valkyrie:
        #     printer(
        #         "{1} latency compilation: {0} seconds\n".format(
        #             self.time_stats.get_latency_compilation(), prefix
        #         )
        #     )
        #     printer(
        #         "{1} latency validation: {0} seconds\n".format(
        #             self.time_stats.get_latency_validation(), prefix
        #         )
        #     )
        #     printer(
        #         "{1} latency plausible: {0} seconds\n".format(
        #             self.time_stats.get_latency_plausible(), prefix
        #         )
        #     )
