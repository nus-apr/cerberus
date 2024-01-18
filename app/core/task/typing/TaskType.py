from typing import Literal
from typing import Union


TaskType = Literal[
    "fuzz", "repair", "composite", "localize", "select", "analyze", "prepare"
]

CompsiteTaskType = Union[TaskType, Literal["crash-analyze"]]
