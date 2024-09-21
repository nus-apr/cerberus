import json
import os
import pathlib
from typing import Any
from typing import List
from typing import Optional
from typing import Sequence

import javalang  # type: ignore

from app.core import container


def read_file(
    container_id: Optional[str], file_path: str, encoding: str = "utf-8"
) -> List[str]:
    file_content = []
    if container_id:
        file_content = container.read_file(container_id, file_path, encoding)
    else:
        with open(file_path, "r", encoding=encoding) as f:
            file_content = f.readlines()
    return file_content


def read_json(
    container_id: Optional[str], file_path: str, encoding: str = "utf-8"
) -> Optional[Any]:
    json_data = None
    file_content = read_file(container_id, file_path, encoding)
    if file_content:
        json_data = json.loads("\n".join(file_content))
    return json_data


def append_file(
    container_id: Optional[str], content: Sequence[str], file_path: str
) -> None:
    if container_id:
        container.append_file(container_id, file_path, content)
    else:
        with open(file_path, "a") as f:
            for line in content:
                f.write(line)


def write_file(
    container_id: Optional[str], content: Sequence[str], file_path: str
) -> None:
    if container_id:
        container.write_file(container_id, file_path, content)
    else:
        with open(file_path, "w") as f:
            for line in content:
                f.write(line)


def write_json(container_id: Optional[str], data: Any, file_path: str) -> None:
    content = json.dumps(data)
    write_file(container_id, [content], file_path)


def list_dir(
    container_id: Optional[str], dir_path: str, regex: Optional[str] = None
) -> List[str]:
    file_list = []
    if container_id:
        if not regex:
            regex = "*"
        if container.is_dir(container_id, dir_path):
            list_files = container.list_dir(container_id, dir_path, regex)
            file_list = [os.path.join(dir_path, t) for t in list_files]
    else:
        if not regex:
            regex = "*"
        if os.path.isdir(dir_path):
            list_files = list(map(str, pathlib.Path(dir_path).rglob(regex)))
            file_list = [os.path.join(dir_path, t) for t in list_files]
    return file_list


def is_dir(container_id: Optional[str], dir_path: str) -> bool:
    if container_id:
        return container.is_dir(container_id, dir_path)
    else:
        return os.path.isdir(dir_path)


def is_file(container_id: Optional[str], file_path: str) -> bool:
    if container_id:
        return container.is_file(container_id, file_path)
    else:
        return os.path.isfile(file_path)


def load_ast_java(
    container_id: Optional[str], file_path: str, encoding: str = "utf-8"
) -> Any:
    if container_id:
        file_object = container.get_file_object(container_id, file_path, encoding)
        tree = javalang.parse.parse(file_object.read())
    else:
        with open(file_path, "r", encoding=encoding) as f:
            tree = javalang.parse.parse(f.read())
    return tree


def load_ast(
    container_id: Optional[str],
    file_path: str,
    encoding: str = "utf-8",
    language: str = "java",
) -> Any:
    if language == "java":
        return load_ast_java(container_id, file_path, encoding)
    else:
        Exception(f"Unsupported Language {language} for AST generation")
    return
