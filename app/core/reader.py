import csv
import json
import os
import pickle


def read_json(file_path: str):
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, "r") as in_file:
            content = in_file.readline()
            json_data = json.loads(content)
    return json_data


def read_pickle(file_path: str):
    pickle_object = None
    if os.path.isfile(file_path):
        with open(file_path, "rb") as pickle_file:
            pickle_object = pickle.load(pickle_file)
    return pickle_object


def read_csv(file_path: str):
    csv_data = None
    if os.path.isfile(file_path):
        with open(file_path, newline="") as csv_file:
            csv_data = csv.DictReader(csv_file)
    return csv_data
