import os
from typing import List

from app.core.env.AbstractEnv import AbstractEnv


class ContainerEnv(AbstractEnv):

    def __init__(self, container_id):
        self.container_id = container_id

    def read_file(self, file_path: str, encoding="utf-8"):
        file_content = container.read_file(self.container_id, file_path, encoding)

    def append_file(self, content: List[str], file_path: str):
        container.append_file(self.container_id, file_path, content)

    def write_file(self, content: List[str], file_path: str):
        container.write_file(self.container_id, file_path, content)

    def list_dir(self, dir_path: str, regex="*"):
        if container.is_dir(self.container_id, dir_path):
            list_files = container.list_dir(self.container_id, dir_path)
            file_list = [os.path.join(dir_path, t) for t in list_files]

    def is_dir(self, dir_path: str):
        container.is_dir(self.container_id, dir_path)

    def is_file(self, file_path: str):
        container.is_file(self.container_id, file_path)