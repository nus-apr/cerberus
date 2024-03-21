from typing import Any
from typing import Dict

from app.core.task.stats.ContainerStats import ContainerStats
from app.core.task.stats.ErrorStats import ErrorStats


class BenchmarkStats:
    # required
    deployed: bool
    configured: bool
    built: bool
    tested: bool
    error_stats: ErrorStats
    container_stats: ContainerStats

    # optional
    include_dependencies_status: bool
    dependencies_compressed: bool

    def __init__(self) -> None:
        self.deployed = False
        self.configured = False
        self.built = False
        self.tested = False
        self.include_dependencies_status = False
        self.dependencies_compressed = False
        self.error_stats = ErrorStats()
        self.container_stats = ContainerStats()

    def get_dict(self) -> Dict[str, Any]:
        summary_general = {
            "deployed": "OK" if self.deployed else "FAILED",
            "configured": "OK" if self.configured else "FAILED",
            "built": "OK" if self.built else "FAILED",
            "tested": "OK" if self.tested else "FAILED",
        }

        if self.include_dependencies_status:
            summary_general["dependencies_compressed"] = (
                "OK" if self.dependencies_compressed else "FAILED"
            )

        summary = {
            "general": summary_general,
            "container": self.container_stats.get_dict(),
        }

        return summary
