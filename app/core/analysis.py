from datetime import datetime


class TimeAnalysis:
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
        if self.__latency_compilation < 0:
            if self.timestamp_compilation:
                self.__latency_compilation = self.compute_latency(
                    str(self.timestamp_compilation)
                )
        return self.__latency_compilation

    def get_latency_validation(self):
        if self.__latency_validation < 0:
            if self.timestamp_validation:
                self.__latency_validation = self.compute_latency(
                    str(self.timestamp_validation)
                )
        return self.__latency_validation

    def get_latency_plausible(self):
        if self.__latency_plausible < 0:
            if self.timestamp_plausible:
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


class SpaceAnalysis:
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


class ErrorAnalysis:
    is_error = False
