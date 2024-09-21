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
    TaskType, Literal["crash-analyze", "bisect", "iterative-repair"]
]


def compare_types(a: CompositeTaskType, b: CompositeTaskType) -> int:
    mapping = {
        "analyze": 0,
        "fuzz": 1,
        "crash-analyze": 2,
        "bisect": 3,
        "slice": 4,
        "localize": 5,
        "repair": 6,
        "validate": 7,
        "select": 8,
        "composite": 9,
        "prepare": 10,
    }
    return mapping[a] - mapping[b]
