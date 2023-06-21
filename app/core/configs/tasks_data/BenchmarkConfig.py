from typing import List


class BenchmarkConfig:

    def __init__(self, name: str, bug_id_list: List[str], bug_id_skip_list: List[str], bug_subjects_list: List[str]):

        self.name = name
        self.bug_id_list = bug_id_list
        self.bug_id_skip_list = bug_id_skip_list
        self.bug_subjects_list = bug_subjects_list

    def get_name(self) -> str:
        return self.name

    def get_bug_id_list(self) -> List[str]:
        return self.bug_id_list

    def get_bug_id_skip_list(self) -> List[str]:
        return self.bug_id_skip_list

    def get_bug_subjects_list(self) -> List[str]:
        return self.bug_subjects_list


    