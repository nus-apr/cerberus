from typing import Dict
from typing import List
from typing import Literal

from app.core.task.typing.TaskType import CompositeTaskType

CompositeSequence = Dict[
    CompositeTaskType,
    List[
        Dict[
            Literal["name", "type", "params", "local", "tag", "ignore", "rebuild"], str
        ]
    ],
]
