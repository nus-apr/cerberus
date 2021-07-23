import abc


class AbstractBenchmark:
    @abc.abstractmethod
    def setup(self, input):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, input):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, input):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, input):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, input):
        """Method documentation"""
        return




