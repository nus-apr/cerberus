from datetime import datetime
from typing import Any
from typing import Dict
from typing import Tuple

from app.core import emitter
from app.core import values
from app.core.task.TaskStatus import TaskStatus


class ContainerStats:
    mem_usage_gb: float
    total_rx_bytes: float
    total_tx_bytes: float
    network_int_count: int

    def __init__(self) -> None:
        self.mem_usage_gb = 0
        self.total_rx_bytes = 0
        self.total_tx_bytes = 0
        self.network_int_count = 0

    @staticmethod
    def compute_cpu_usage(container_stats: Dict[str, Any]) -> float:
        cpu_usage_delta = (
            container_stats["cpu_stats"]["cpu_usage"]["total_usage"]
            - container_stats["precpu_stats"]["cpu_usage"]["total_usage"]
        )
        system_cpu_usage_delta = (
            container_stats["cpu_stats"]["system_cpu_usage"]
            - container_stats["precpu_stats"]["system_cpu_usage"]
        )

        percentage_usage = 0
        if system_cpu_usage_delta != 0:
            round(
                (cpu_usage_delta / system_cpu_usage_delta)
                * container_stats["cpu_stats"]["online_cpus"]
                * 100,
                3,
            )

        return percentage_usage

    @staticmethod
    def compute_network_usage(container_stats: Dict[str, Any]) -> Tuple[int, int, int]:
        networks = container_stats.get("networks", {})
        nr_network_interfaces = len(networks)
        total_rx_bytes = 0
        total_tx_bytes = 0

        for _, network_obj in networks.items():
            total_rx_bytes += network_obj["rx_bytes"]
            total_tx_bytes += network_obj["tx_bytes"]

        return nr_network_interfaces, total_rx_bytes, total_tx_bytes

    def load_container_stats(self, container_stats: Dict[str, Any]) -> None:
        emitter.debug(container_stats)
        self.mem_usage_gb = round(
            container_stats["memory_stats"].get(
                "max_usage", container_stats["memory_stats"].get("usage", 0)
            )
            / (1024 * 1024 * 1024),
            3,
        )
        (
            self.network_int_count,
            self.total_rx_bytes,
            self.total_tx_bytes,
        ) = ContainerStats.compute_network_usage(container_stats)

    def get_dict(self) -> Dict[str, Any]:

        return {
            "mem_usage": f"{self.mem_usage_gb} GiB",
            "network_usage": {
                "total_received": f"{self.total_rx_bytes} bytes",
                "total_transmitted": f"{self.total_tx_bytes} bytes",
                "interfaces_count": self.network_int_count,
            },
        }
