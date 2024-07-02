from typing import Literal
from typing import Union


TaskType = Literal[
    "fuzz",
    "repair",
    "composite",
    "localize",
    "select",
    "analyze",
    "prepare",
    "slice",
    "validate",
]

CompositeTaskType = Union[
    TaskType, Literal["crash-analyze"], Literal["iterative-repair"]
]


def compare_types(a: CompositeTaskType, b: CompositeTaskType) -> int:
    mapping = {
        "analyze": 0,
        "fuzz": 1,
        "crash-analyze": 2,
        "slice": 3,
        "localize": 4,
        "repair": 5,
        "validate": 6,
        "select": 7,
        "composite": 8,
        "prepare": 9,
    }
    return mapping[a] - mapping[b]
