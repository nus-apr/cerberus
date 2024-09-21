from typing import Dict


class PatchStats:
    non_compilable: int = -1
    malformed: int = -1
    plausible: int = -1
    generated: int = -1
    size: int = -1
    enumerations: int = -1
    correct: int = -1
    high_quality: int = -1
    incorrect: int = -1
    fix_fail: int = -1
    __implausible: int = -1

    def get_exploration_ratio(self) -> float:
        return (self.enumerations / self.size) * 100

    def get_implausible(self) -> int:
        if self.__implausible == -1 and self.enumerations > 0:
            self.__implausible = (
                self.enumerations - self.plausible - self.non_compilable
            )
        return self.__implausible

    def get_dict(self, is_validate: bool = False) -> Dict[str, int]:
        if is_validate:
            summary = {
                "search space": self.size,
                "enumerations": self.enumerations,
                "malformed": self.malformed,
                "build failed": self.non_compilable,
                "fixed fail": self.fix_fail,
                "incorrect": self.incorrect,
                "plausible": self.plausible,
                "correct": self.correct,
                "high_quality": self.high_quality,
            }
        else:
            summary = {
                "search space": self.size,
                "enumerations": self.enumerations,
                "non-compilable": self.non_compilable,
                "plausible": self.plausible,
                "implausible": self.get_implausible(),
                "generated": self.generated,
            }
        return summary
