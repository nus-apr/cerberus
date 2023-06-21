import os
from abc import ABC


class TaskAbstractDirsInfo(ABC):

    def __init__(self, dir_exp, dir_setup, dir_aux, dir_base, dir_logs, dir_artifact):
        self.dir_exp = self._init_dir(dir_exp)
        self.dir_setup = self._init_dir(dir_setup)
        self.dir_aux = self._init_dir(dir_aux)
        self.dir_base = self._init_dir(dir_base)
        self.dir_logs = self._init_dir(dir_logs)
        self.dir_artifact = self._init_dir(dir_artifact)

    @staticmethod
    def _init_dir(dir_path):
        os.makedirs(dir_path, exist_ok=True)
        return dir_path

    def get_dir_exp(self):
        return self.dir_exp
