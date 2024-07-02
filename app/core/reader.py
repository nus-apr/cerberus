import csv
import json
import os
import pickle
from typing import Any
from typing import Optional

import yaml


def read_json(file_path: str) -> Optional[Any]:
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, "r") as in_file:
            content = in_file.readlines()
            if len(content) > 1:
                content_str = " ".join([l.strip().replace("\n", "") for l in content])
            else:
                content_str = content[0]
            json_data = json.loads(content_str)
    return json_data


def read_pickle(file_path: str) -> Optional[Any]:
    pickle_object = None
    if os.path.isfile(file_path):
        with open(file_path, "rb") as pickle_file:
            pickle_object = pickle.load(pickle_file)
    return pickle_object


def read_yaml(file_path: str) -> Optional[Any]:
    yaml_data = None
    if os.path.isfile(file_path):
        with open(file_path, "r") as yaml_file:
            yaml_data = yaml.safe_load(yaml_file)
    return yaml_data


def read_csv(file_path: str) -> Optional[Any]:
    csv_data = None
    if os.path.isfile(file_path):
        with open(file_path, newline="") as csv_file:
            csv_data = csv.DictReader(csv_file)
    return csv_data
