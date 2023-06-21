import json
from jsonschema.validators import Draft7Validator
import jsonschema


class ConfigDataLoader:

    def __init__(self, file_path: str, validation_schema: dict):
        self._file_path = file_path
        self._validation_schema = validation_schema
        self.config_data = None

    def load(self):
        try:
            with open(self._file_path) as json_desc:
                self.config_data = json.load(json_desc)
        except FileNotFoundError:
            raise FileNotFoundError(f"Config file '{self._file_path}' doesn't exist.")
        except json.JSONDecodeError as e:
            raise ValueError(f"File '{self._file_path}' is not JSON valid. Error {e}")

    def validate(self):
        validator = Draft7Validator(self._validation_schema)
        errors = list(validator.iter_errors(self.config_data))
        if len(errors) != 0:
            for error in errors:
                print(error.message)
            raise ValueError("Config is not valid.")

    def get_config_data(self):
        return self.config_data
