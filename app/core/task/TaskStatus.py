from enum import Enum


class TaskStatus(Enum):
    NONE = -1
    SUCCESS = 0
    FAIL = 1
    PREPROCESSING = 2
    REPAIRING = 3
    EXTRACTING_PATCHES = 4
    PREPARING_IMAGE = 5
    FAIL_IN_SETUP = 6
    FAIL_IN_DEPLOY = 7
    FAIL_IN_CONFIG = 8
    FAIL_IN_BUILD = 9
    FAIL_IN_TEST = 10
    FAIL_IN_VERIFY = 11
    FAIL_IN_INSTRUMENT = 12
    FAIL_IN_TOOL = 13
    CANCELLED = 14
    VALIDATING = 15
    TIMEOUT = 16

    def __str__(self) -> str:
        response_map = {
            TaskStatus.SUCCESS: "Success",
            TaskStatus.FAIL: "Failure",
            TaskStatus.PREPROCESSING: "Preprocessing",
            TaskStatus.REPAIRING: "Repairing",
            TaskStatus.EXTRACTING_PATCHES: "Extracting Patches",
            TaskStatus.PREPARING_IMAGE: "Preparing image",
            TaskStatus.FAIL_IN_SETUP: "Failed in image setup phase",
            TaskStatus.FAIL_IN_DEPLOY: "Failed in image deploy phase",
            TaskStatus.FAIL_IN_BUILD: "Failed in image building phase",
            TaskStatus.FAIL_IN_CONFIG: "Failed in image configuration phase",
            TaskStatus.FAIL_IN_TEST: "Failed in image testing phase",
            TaskStatus.FAIL_IN_VERIFY: "Failed in image verification phase",
            TaskStatus.FAIL_IN_INSTRUMENT: "Failed in image instrumentation phase",
            TaskStatus.FAIL_IN_TOOL: "Tool returned non-zero status",
            TaskStatus.CANCELLED: "Job Cancelled",
            TaskStatus.VALIDATING: "Tool validating patches",
            TaskStatus.TIMEOUT: "Job Timeout",
            TaskStatus.NONE: "NONEEEEEE",
        }
        if self in response_map:
            return response_map[self]
        else:
            raise NotImplementedError("New status defined but not implemented in repr")
