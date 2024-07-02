from typing import Dict


class ReportStats:
    generated: int = -1

    def get_dict(self) -> Dict[str, int]:
        summary = {"generated": self.generated}
        return summary
