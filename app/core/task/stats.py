from datetime import datetime

from app.core import emitter
from app.core import values
from app.core.task.status import TaskStatus


class ToolTimeStats:
    timestamp_start = "Wed 20 Jul 2022 10:31:47 AM +08"
    timestamp_end = "Wed 20 Jul 2022 10:31:47 AM +08"
    timestamp_compilation = 0
    timestamp_validation = 0
    timestamp_plausible = 0
    total_validation: float = 0.0
    total_build: float = 0.0
    __latency_compilation = -1
    __latency_validation = -1
    __latency_plausible = -1
    __default_time_fmt = "%a %d %b %Y %H:%M:%S %p"
    __log_time_fmt = None
    __duration_total = -1

    def compute_duration(self, start_time: str, end_time: str):
        # Fri 08 Oct 2021 04:59:55 PM +08
        start_time = start_time.split(" +")[0].strip()
        end_time = end_time.split(" +")[0].strip()
        tstart = datetime.strptime(start_time, self.__default_time_fmt)
        tend = datetime.strptime(end_time, self.__default_time_fmt)
        duration = (tend - tstart).total_seconds()
        return duration

    def compute_latency(self, time: str):
        # Fri 08 Oct 2021 04:59:55 PM +08
        # 2022-Apr-07 04:38:46.994352
        # fmt_1 = '%a %d %b %Y %H:%M:%S %p'
        # fmt_2 = '%Y-%m-%d %H:%M:%S.%f'
        start_time_str = self.timestamp_start.split(" +")[0].strip()
        end_time_str = time.split(" +")[0].strip()
        tstart = datetime.strptime(start_time_str, self.__default_time_fmt)
        tend = datetime.strptime(
            end_time_str, self.__default_time_fmt
        )  # was log_time_fmt
        duration = (tend - tstart).total_seconds()
        return duration

    def set_log_time_fmt(self, time_fmt: str):
        self.__log_time_fmt = time_fmt

    def get_duration(self):
        if self.__duration_total < 0:
            self.__duration_total = self.compute_duration(
                self.timestamp_start, self.timestamp_end
            )
        return self.__duration_total

    def get_latency_compilation(self):
        if self.__latency_compilation < 0 and self.timestamp_compilation:
            self.__latency_compilation = self.compute_latency(
                str(self.timestamp_compilation)
            )
        return self.__latency_compilation

    def get_latency_validation(self):
        if self.__latency_validation < 0 and self.timestamp_validation:
            self.__latency_validation = self.compute_latency(
                str(self.timestamp_validation)
            )
        return self.__latency_validation

    def get_latency_plausible(self):
        if self.__latency_plausible < 0 and self.timestamp_plausible:
            self.__latency_plausible = self.compute_latency(
                str(self.timestamp_plausible)
            )
        return self.__latency_plausible

    def get_array(self):
        summary = {
            "total duration": self.get_duration(),
            "build time": self.total_build,
            "validation time": self.total_validation,
        }
        return summary


class ToolPatchesStats:
    non_compilable: int = 0
    plausible: int = 0
    generated: int = 0
    size: int = 0
    enumerations: int = 0
    __implausible = None

    def get_implausible(self):
        if self.__implausible is None:
            self.__implausible = (
                self.enumerations - self.plausible - self.non_compilable
            )
        return self.__implausible

    def get_exploration_ratio(self):
        return (self.enumerations / self.size) * 100

    def get_array(self):
        summary = {
            "search space": self.size,
            "enumerations": self.enumerations,
            "non-compilable": self.non_compilable,
            "plausible": self.plausible,
            "implausible": self.get_implausible(),
            "generated": self.generated,
        }
        return summary


class ErrorStats:
    is_error = False


class ContainerStats:
    mem_usage_gb: float
    total_rx_bytes: float
    total_tx_bytes: float
    network_int_count: int

    def __init__(self):
        self.mem_usage_gb = 0
        self.total_rx_bytes = 0
        self.total_tx_bytes = 0
        self.network_int_count = 0

    @staticmethod
    def compute_cpu_usage(container_stats: dict):
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
    def compute_network_usage(container_stats: dict):
        networks = container_stats["networks"]
        nr_network_interfaces = len(networks)
        total_rx_bytes = 0
        total_tx_bytes = 0

        for _, network_obj in networks.items():
            total_rx_bytes += network_obj["rx_bytes"]
            total_tx_bytes += network_obj["tx_bytes"]

        return nr_network_interfaces, total_rx_bytes, total_tx_bytes

    def load_container_stats(self, container_stats: dict):
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

    def get_array(self):

        return {
            "mem_usage": f"{self.mem_usage_gb} GiB",
            "network_usage": {
                "total_received": f"{self.total_rx_bytes} bytes",
                "total_transmitted": f"{self.total_tx_bytes} bytes",
                "interfaces_count": self.network_int_count,
            },
        }


class ToolStats:
    time_stats: ToolTimeStats
    patches_stats: ToolPatchesStats
    container_stats: ContainerStats
    error_stats: ErrorStats

    def __init__(self):
        self.time_stats = ToolTimeStats()
        self.patches_stats = ToolPatchesStats()
        self.container_stats = ContainerStats()
        self.error_stats = ErrorStats()

    def reset(self):
        self.time_stats = ToolTimeStats()
        self.patches_stats = ToolPatchesStats()
        self.container_stats = ContainerStats()
        self.error_stats = ErrorStats()

    def get_array(self):
        return {
            "status": str(values.experiment_status.get(TaskStatus.NONE)),
            "details": {
                "time": self.time_stats.get_array(),
                "space": self.patches_stats.get_array(),
                "container": self.container_stats.get_array(),
            },
        }


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

    def __init__(self):
        self.deployed = False
        self.configured = False
        self.built = False
        self.tested = False
        self.include_dependencies_status = False
        self.dependencies_compressed = False
        self.error_stats = ErrorStats()
        self.container_stats = ContainerStats()

    def get_array(self):
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
            "container": self.container_stats.get_array(),
        }

        return summary
