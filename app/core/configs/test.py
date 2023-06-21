# Define the first schema with required fields and no additional properties
import copy
import json

from jsonschema.validators import Draft7Validator

schema1 = {
    "type": "object",
    "properties": {
        "field1": {"type": "string"},
        "field2": {"type": "number"}
    },
    "required": ["field1", "field2"],
    "additionalProperties": False
}

# Define the second schema inline by extending schema1
schema2 = {
    "allOf": [
        schema1,
        {
            "type": "object",
            "properties": {
                "field3": {"type": "boolean"},
                "field4": {"type": "array", "items": {"type": "string"}}
            },
            "required": ["field3", "field4"],
            "additionalProperties": schema1["additionalProperties"]
        }
    ]
}

schema3 = copy.deepcopy(schema1)
schema3["properties"].update(
        {
            "field3": {"type": "boolean"},
            "field4": {"type": "array", "items": {"type": "string"}}
        }
)
schema3["required"] = ["field3", "field4"]


schema3 = {
    "properties": {
        **schema3["properties"],
        "field3": {"type": "boolean"},
        "field4": {"type": "array", "items": {"type": "string"}}
    },
    "required": ["field3", "field4"],
    "additionalProperties": False
}

# Example data to validate against schema2
data = {
    "field1": "Value 1",
    "field3": True,
    "field4": ["str"]
}

# Validate the data against schema2
print(json.dumps(schema3, indent=4))
validator = Draft7Validator(schema3)
errors = list(validator.iter_errors(data))

# Print the errors, if any
if errors:
    print("Validation failed. Errors:")
    for error in errors:
        print(error.message)
else:
    print("Validation successful.")
