import json
from typing import Any
from typing import Dict
from typing import List

import jsonschema
from jsonschema.validators import Draft7Validator


class MetadataLoader:
    def __init__(self, file_path: str, validation_schema: Dict[Any, Any]) -> None:
        self._file_path = file_path
        self._validation_schema = validation_schema
        self.meta_data = None

    def load(self) -> None:
        try:
            with open(self._file_path) as json_desc:
                self.meta_data = json.load(json_desc)
                if not isinstance(self.meta_data, List):
                    raise ValueError(
                        "File '{self._file_path}' does not provide a List."
                    )
        except FileNotFoundError:
            raise FileNotFoundError(f"Metadata file '{self._file_path}' doesn't exist.")
        except json.JSONDecodeError as e:
            raise ValueError(f"File '{self._file_path}' is not JSON valid. Error {e}")

    def validate(self) -> None:
        validator = Draft7Validator(self._validation_schema)
        errors = list(validator.iter_errors(self.meta_data))
        if len(errors) != 0:
            for error in errors:
                print(error.message)
                print(error.path)
            raise ValueError("Metadata is not valid.")

    def get_meta_data(self) -> List[Dict[str, Any]]:
        if self.meta_data is None:
            raise ValueError("Metadata is not loaded.")
        return self.meta_data
