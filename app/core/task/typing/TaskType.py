from typing import Literal


TaskType = Literal[
    "fuzz", "repair", "composite", "localize", "select", "analyze", "prepare"
]
