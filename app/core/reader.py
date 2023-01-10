import json
import pickle
import os


def read_json(file_path):
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, "r") as in_file:
            content = in_file.readline()
            json_data = json.loads(content)
    return json_data


def read_pickle(file_path):
    pickle_object = None
    if os.path.isfile(file_path):
        with open(file_path, "rb") as pickle_file:
            pickle_object = pickle.load(pickle_file)
    return pickle_object
