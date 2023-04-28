from typing import Dict
from typing import Literal
from typing import Tuple

from app.core.task.stats import ErrorStats
from app.core.task.stats import SpaceStats
from app.core.task.stats import TimeStats


DirectoryInfo = Dict[Literal["local", "container"], Dict[str, str]]
ResultInfo = Tuple[SpaceStats, TimeStats, ErrorStats]
