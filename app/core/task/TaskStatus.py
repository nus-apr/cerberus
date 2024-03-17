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

    def __str__(self) -> str:
        if self.value == self.SUCCESS:
            return "Success"
        elif self.value == self.FAIL:
            return "Failure"
        elif self.value == self.PREPROCESSING:
            return "Preprocessing"
        elif self.value == self.REPAIRING:
            return "Repairing"
        elif self.value == self.EXTRACTING_PATCHES:
            return "Extracting Patches"
        elif self.value == self.PREPARING_IMAGE:
            return "Preparing image"
        elif self.value == self.FAIL_IN_SETUP:
            return "Failed in image setup phase"
        elif self.value == self.FAIL_IN_DEPLOY:
            return "Failed in image deploy phase"
        elif self.value == self.FAIL_IN_BUILD:
            return "Failed in image building phase"
        elif self.value == self.FAIL_IN_CONFIG:
            return "Failed in image configuration phase"
        elif self.value == self.FAIL_IN_TEST:
            return "Failed in image testing phase"
        elif self.value == self.FAIL_IN_VERIFY:
            return "Failed in image verification phase"
        elif self.value == self.FAIL_IN_INSTRUMENT:
            return "Failed in image instrumentation phase"
        elif self.value == self.FAIL_IN_TOOL:
            return "Tool returned non-zero status"
        elif self.value == self.CANCELLED:
            return "Job Cancelled"
        elif self.value == self.VALIDATING:
            return "Tool validating patches"
        elif self.value == self.NONE:
            return "NONEEEEEE"
        else:
            raise NotImplementedError("New status defined but not implemented in repr")
