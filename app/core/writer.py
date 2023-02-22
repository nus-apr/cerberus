#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import json
import pickle
from typing import Any


def write_as_json(data: Any, output_file_path: str):
    content = json.dumps(data)
    with open(output_file_path, "w") as out_file:
        out_file.writelines(content)


def write_as_pickle(data: Any, output_file_path: str):
    with open(output_file_path, "wb") as out_file:
        pickle.dump(data, out_file)
