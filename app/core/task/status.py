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

    def __str__(self) -> str:
        if self is self.SUCCESS:
            return "Success"
        elif self is self.FAIL:
            return "Failure"
        elif self is self.PREPROCESSING:
            return "Preprocessing"
        elif self is self.REPAIRING:
            return "Repairing"
        elif self is self.EXTRACTING_PATCHES:
            return "Extracting Patches"
        elif self is self.PREPARING_IMAGE:
            return "Preparing image"
        elif self is self.FAIL_IN_SETUP:
            return "Failed in image setup phase"
        elif self is self.FAIL_IN_DEPLOY:
            return "Failed in image deploy phase"
        elif self is self.FAIL_IN_BUILD:
            return "Failed in image building phase"
        elif self is self.FAIL_IN_CONFIG:
            return "Failed in image configuration phase"
        elif self is self.FAIL_IN_TEST:
            return "Failed in image testing phase"
        elif self is self.FAIL_IN_VERIFY:
            return "Failed in image verification phase"
        elif self is self.FAIL_IN_INSTRUMENT:
            return "Failed in image instrumentation phase"
        elif self is self.FAIL_IN_TOOL:
            return "Tool returned non-zero status"
        elif self is self.CANCELLED:
            return "Job Cancelled"
        elif self is self.NONE:
            return "NONEEEEEE"
        else:
            raise NotImplementedError("New status defined but not implemented in repr")
