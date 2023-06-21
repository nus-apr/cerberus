import json
from abc import ABC, abstractmethod
from typing import Any, List


class AbstractEnv(ABC):

    @abstractmethod
    def read_file(self, file_path: str, encoding="utf-8"):
        pass

    @abstractmethod
    def append_file(self, content: List[str], file_path: str):
        pass

    @abstractmethod
    def write_file(self, content: List[str], file_path: str):
        pass

    @abstractmethod
    def list_dir(self,  dir_path: str, regex="*"):
        pass

    @abstractmethod
    def is_dir(self, dir_path: str):
        pass

    @abstractmethod
    def is_file(self, file_path: str):
        pass

    def read_json(self, file_path: str, encoding="utf-8"):
        json_data = None
        file_content = self.read_file(file_path, encoding)
        if file_content:
            json_data = json.loads("\n".join(file_content))
        return json_data

    def write_json(self, data: Any, file_path: str):
        content = json.dumps(data)
        self.write_file([content], file_path)