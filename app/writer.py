#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import pickle
import json


def write_as_json(data, output_file_path):
    content = json.dumps(data)
    with open(output_file_path, "w") as out_file:
        out_file.writelines(content)


def write_as_pickle(data, output_file_path):
    with open(output_file_path, "wb") as out_file:
        pickle.dump(data, out_file)
