from app.core.BenchmarkNamesEnum import BenchmarkNamesEnum
from app.drivers.benchmarks.java.Vul4J import Vul4J


class BenchmarkLoader:

    @staticmethod
    def load_benchmark(benchmark_name: str):

        # maybe use cache

        if benchmark_name == BenchmarkNamesEnum.VUL4J.value:
            return Vul4J()
        else:
            raise ValueError("No such benchmark")
