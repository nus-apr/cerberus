import json
import os
from os.path import join
from typing import cast

from app.core.dirs.BaseDirsInfo import BaseDirsInfo


class AbstractBenchmark:

    def __init__(self, name, base_dirs_info: BaseDirsInfo):
        self.name = name
        self.base_dirs_info = base_dirs_info

        self.experiments_subjects = self.load_meta_file()

        #stats

    def load_meta_file(self) -> dict:

        meta_file_path = join(self.base_dirs_info.get_benchmark_dir(), self.name, "meta-data.json")
        if not meta_file_path:
            raise ValueError("Meta file path not set")
        if not os.path.isfile(cast(str, meta_file_path)):
            raise ValueError("Meta file does not exist")
        with open(cast(str, meta_file_path), "r") as in_file:
            json_data = json.load(in_file)
            if json_data:
                return json_data
            else:
                raise ValueError("Could not load meta-data from")
                # error
