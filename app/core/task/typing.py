from typing import Dict
from typing import Literal


DirectoryInfo = Dict[Literal["local", "container"], Dict[str, str]]
TaskType = Literal["fuzz", "repair", "analyze", "prepare"]
