import os
import pathlib
from typing import List

from app.core.env.AbstractEnv import AbstractEnv


class LocalEnv(AbstractEnv):
    def read_file(self, file_path: str, encoding="utf-8"):
        with open(file_path, "r", encoding=encoding) as f:
            return f.readlines()

    def append_file(self, content: List[str], file_path: str):
        with open(file_path, "a") as f:
            for line in content:
                f.write(line)

    def write_file(self, content: List[str], file_path: str):
        with open(file_path, "w") as f:
            for line in content:
                f.write(line)

    def list_dir(self, dir_path: str, regex="*"):
        file_list = []
        if os.path.isdir(dir_path):
            list_files = list(pathlib.Path(dir_path).rglob(regex))
            file_list = [os.path.join(dir_path, t) for t in list_files]
        return file_list

    def is_dir(self, dir_path: str):
        return os.path.isdir(dir_path)

    def is_file(self, file_path: str):
        return os.path.isfile(file_path)