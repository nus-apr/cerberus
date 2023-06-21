import argparse
import copy
import json
import os
import sys
from os.path import dirname, join

from app.core.configs.Config import Config
from app.core.configs.ConfigDataFactory import ConfigDataFactory
from app.core.configs.ConfigDataLoader import ConfigDataLoader
from app.core.configs.ConfigValidationSchema import config_validation_schema
from app.core.dirs.BaseDirsInfo import BaseDirsInfo
from app.core.emitter.Emitter import Emitter
from app.core.tasks.TaskDataFactory import TaskDataFactory


class Cerberus:
    config: Config

    def __init__(self, config_file_path: str):
        self._init_config(config_file_path)

        self.base_dirs_info = BaseDirsInfo(os.path.realpath(dirname(__file__)))

        self.emitter = Emitter(self.config.get_general(), self.base_dirs_info)

    def _init_config(self, config_file_path: str):
        config_loader = ConfigDataLoader(file_path=config_file_path, validation_schema=config_validation_schema)
        config_loader.load()
        config_loader.validate()
        self.config = ConfigDataFactory.create(config_data_dict=config_loader.get_config_data())

    def get_task_queue(self):
        task_data_factory = TaskDataFactory.get_tasks_queue(self.config)


    def get_config(self):
        return self.config

    # start cerberus
    def start(self):

        self.emitter.title("Starting Cerberus (Program Repair Framework)")

        # print configuration
        self.emitter.sub_title("General Configuration")
        self.emitter.configuration(self.config.get_general())


        # load tasks -> x tasks
        self.emitter.sub_title("Loading Tasks")
        self.emitter.information("Loaded 23 Tasks")



def main():
    parser = argparse.ArgumentParser(prog="Cerberus", usage="%(prog)s [options]")
    parser.add_argument('-f', '--config-file', type=str, help='Path to the JSON config file')
    args = parser.parse_args()

    cerberus = Cerberus(args.config_file)
    cerberus.start()


if __name__ == "__main__":
    main()
