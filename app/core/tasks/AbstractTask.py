import hashlib
import time
from abc import ABC, abstractmethod
from re import A

from app.core import definitions
from typing import Dict, Any, Optional

from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


class AbstractTask(ABC):

    @abstractmethod
    def run(self):
        pass
