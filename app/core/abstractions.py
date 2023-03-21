import json
import os
import pathlib
from typing import Any
from typing import Dict
from typing import List
from typing import Optional

from app.core import container


def read_file(container_id: Optional[str], file_path: str, encoding="utf-8"):
    file_content = []
    if container_id:
        file_content = container.read_file(container_id, file_path, encoding)
    else:
        with open(file_path, "r", encoding=encoding) as f:
            file_content = f.readlines()
    return file_content


def read_json(container_id: Optional[str], file_path: str, encoding="utf-8"):
    json_data = None
    file_content = read_file(container_id, file_path, encoding)
    if file_content:
        json_data = json.loads("\n".join(file_content))
    return json_data


def append_file(container_id: Optional[str], content: List[str], file_path: str):
    if container_id:
        container.append_file(container_id, file_path, content)
    else:
        with open(file_path, "a") as f:
            for line in content:
                f.write(line)


def write_file(container_id: Optional[str], content: List[str], file_path: str):
    if container_id:
        container.write_file(container_id, file_path, content)
    else:
        with open(file_path, "w") as f:
            for line in content:
                f.write(line)


def write_json(container_id: Optional[str], data: Any, file_path: str):
    content = json.dumps(data)
    write_file(container_id, [content], file_path)


def list_dir(container_id: Optional[str], dir_path: str, regex=None):
    file_list = []
    if not regex:
        regex = "*"
    if container_id:
        if container.is_dir(container_id, dir_path):
            list_files = container.list_dir(container_id, dir_path)
            file_list = [os.path.join(dir_path, t) for t in list_files]
    else:
        if os.path.isdir(dir_path):
            list_files = list(pathlib.Path(dir_path).rglob(regex))
            file_list = [os.path.join(dir_path, t) for t in list_files]
    return file_list


def is_dir(container_id: Optional[str], dir_path: str):
    if container_id:
        return container.is_dir(container_id, dir_path)
    else:
        return os.path.isdir(dir_path)


def is_file(container_id: Optional[str], file_path: str):
    if container_id:
        return container.is_file(container_id, file_path)
    else:
        return os.path.isfile(file_path)
