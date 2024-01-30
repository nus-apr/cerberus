from typing import Literal
from typing import Union


TaskType = Literal[
    "fuzz",
    "repair",
    "composite",
    "localize",
    "validate",
    "select",
    "analyze",
    "prepare",
]

CompositeTaskType = Union[TaskType, Literal["crash-analyze"]]
