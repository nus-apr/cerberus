from typing import Any
from typing import cast
from typing import Dict

from app.core.metadata.MetadataFieldsEnum import MetadataFieldsEnum

"""
Entrypoint schema
"""
entrypoint_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.ROOT_ABSPATH.value: {
            "type": "string",
            "pattern": "/[a-z0-9A-Z/_.\\-]*",
        },
        MetadataFieldsEnum.ENTRYPOINT.value: {
            "type": "object",
            "properties": {
                MetadataFieldsEnum.FILE.value: {"type": "string"},
                MetadataFieldsEnum.FUNCTION.value: {"type": "string"},
            },
            "required": [
                # MetadataFieldsEnum.FILE.value,
                # MetadataFieldsEnum.FUNCTION.value,
            ],
            "additionalProperties": False,
        },
        "required": [],
        "additionalProperties": False,
    },
}

"""
File Source Schema
"""
src_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.ROOT_ABSPATH.value: {"type": "string"},
        MetadataFieldsEnum.ENTRYPOINT.value: entrypoint_schema,
    },
    "additionalProperties": False,
}

"""
Localization Schema
"""
localization_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.SOURCE_FILE.value: {"type": "string"},
        MetadataFieldsEnum.LINE_NUMBERS.value: {
            "type": "array",
            "items": {"type": "number", "minimum": 1},
        },
        MetadataFieldsEnum.FUNCTION.value: {"type": "string"},
        MetadataFieldsEnum.SCORE.value: {
            "type": "number",
            "minimum": 0,
            "maximum": 1,
        },
    },
    "required": [
        MetadataFieldsEnum.SOURCE_FILE.value,
        MetadataFieldsEnum.LINE_NUMBERS.value,
    ],
    "additionalProperties": True,
}

"""
Stack Trace Schema
"""
stack_trace_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.DEPTH.value: {"type": "number"},
        MetadataFieldsEnum.SOURCE_FILE.value: {"type": "string"},
        MetadataFieldsEnum.FUNCTION.value: {"type": "string"},
        MetadataFieldsEnum.LINE.value: {"type": "number"},
    },
}

"""
Output data Schema
"""
output_data_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.FORMAT.value: {"type": "string"},
        MetadataFieldsEnum.DIR.value: {"type": "string"},
    },
    "required": [MetadataFieldsEnum.FORMAT.value, MetadataFieldsEnum.DIR.value],
}

"""
Analysis Output Schema
"""
analysis_output_schema = {
    "type": "array",
    "items": {
        "type": "object",
        "properties": {
            MetadataFieldsEnum.BUG_TYPE.value: {"type": "string"},
            MetadataFieldsEnum.GENERATOR.value: {"type": "string"},
            MetadataFieldsEnum.CONFIDENCE.value: {
                "type": "number",
                "minimum": 0,
                "maximum": 1,
            },
            MetadataFieldsEnum.STACK_TRACE.value: {
                "type": "array",
                "items": stack_trace_schema,
            },
            MetadataFieldsEnum.BENIGN_INPUTS.value: {
                "type": "array",
                "items": output_data_schema,
            },
            MetadataFieldsEnum.EXPLOIT_INPUTS.value: {
                "type": "array",
                "items": output_data_schema,
            },
            #   MetadataFieldsEnum.PARSING.value: {"type": "string"},
            #   MetadataFieldsEnum.CORRECT.value: {"type": "boolean"},
            #   MetadataFieldsEnum.ORDERED_PATCHES.value: {"type": "array", "items": {"type": "string"}},
            #   MetadataFieldsEnum.MESSAGE.value: {"type": "string"},
        },
        "additionalProperties": True,
        "required": [MetadataFieldsEnum.GENERATOR.value],
    },
}


"""
Validation Schema
"""
validation_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.NON_PARSING.value: {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    MetadataFieldsEnum.ID.value: {"type": "string"},
                    MetadataFieldsEnum.MESSAGE.value: {"type": "string"},
                },
            },
        },
        MetadataFieldsEnum.PARSING.value: {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    MetadataFieldsEnum.ID.value: {"type": "string"},
                    MetadataFieldsEnum.FAILIING.value: {
                        "type": "object",
                        "properties": {
                            MetadataFieldsEnum.MESSAGE.value: {"type": "string"},
                            MetadataFieldsEnum.FAILING_TEST_ID.value: {
                                "type": "string"
                            },
                        },
                    },
                    MetadataFieldsEnum.PASSING_TEST_IDS.value: {
                        "type": "array",
                        "items": {"type": "string"},
                    },
                },
            },
        },
        MetadataFieldsEnum.PLAUSIBLE: {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    MetadataFieldsEnum.ID.value: {"type": "string"},
                    MetadataFieldsEnum.PASSING_TEST_IDS.value: {
                        "type": "array",
                        "items": {"type": "string"},
                    },
                },
            },
        },
    },
}


"""
Bug Info Schema
"""
bug_info_schema = {
    "type": "object",
    "properties": {
        MetadataFieldsEnum.ID.value: {"type": "number"},
        MetadataFieldsEnum.SUBJECT.value: {"type": "string"},
        MetadataFieldsEnum.BUG_ID.value: {"type": "string"},
        MetadataFieldsEnum.LANGUAGE.value: {"type": "string"},
        MetadataFieldsEnum.SETUP_SCRIPT.value: {"type": "string"},
        MetadataFieldsEnum.CONFIG_SCRIPT.value: {"type": "string"},
        MetadataFieldsEnum.BUILD_SCRIPT.value: {"type": "string"},
        MetadataFieldsEnum.SRC.value: src_schema,
        MetadataFieldsEnum.COUNT_POS.value: {"type": "number", "minimum": 0},
        MetadataFieldsEnum.COUNT_NEG.value: {"type": "number", "minimum": 0},
        MetadataFieldsEnum.TEST_TIMEOUT.value: {
            "type": "number",
            "minimum": 0,
            "maximum": 100,
        },
        MetadataFieldsEnum.BUG_TYPE.value: {"type": "string"},
        MetadataFieldsEnum.PASSING_TEST_IDS.value: {
            "type": "array",
            "items": {"type": "string"},
        },
        MetadataFieldsEnum.FAILING_TEST_IDS.value: {
            "type": "array",
            "items": {"type": "string"},
        },
        MetadataFieldsEnum.TEST_SCRIPT.value: {"type": "string"},
        MetadataFieldsEnum.BUILD_COMMAND.value: {"type": "string"},
        MetadataFieldsEnum.BINARY_ARGS.value: {"type": "string"},
        MetadataFieldsEnum.BINARY_PATH.value: {"type": "string"},
        MetadataFieldsEnum.LOCALIZATION.value: {
            "type": "array",
            "items": localization_schema,
        },
        MetadataFieldsEnum.OUTPUT_DIR_ABSPATH.value: {"type": "string"},
        MetadataFieldsEnum.EXPLOIT_INPUTS.value: {
            "type": "array",
            "items": {"type": "string"},
        },
        MetadataFieldsEnum.BENIGN_INPUTS.value: {
            "oneof": [
                {
                    "type": "array",
                    "items": {"type": "string"},
                },
                output_data_schema,
            ]
        },
        MetadataFieldsEnum.CRASH_STACK_TRACE.value: {
            "oneof": [
                {
                    "type": "array",
                    "items": {"type": "string"},
                },
                output_data_schema,
            ]
        },
        MetadataFieldsEnum.ANALYSIS_OUTPUT.value: analysis_output_schema,
        MetadataFieldsEnum.PATCHES_DIR.value: {"type": "string"},
        MetadataFieldsEnum.PLAUIBLE_PATCHES_DIR: {"type": "string"},
    },
    "required": [
        MetadataFieldsEnum.ID.value,
        MetadataFieldsEnum.SUBJECT.value,
        MetadataFieldsEnum.CONFIG_SCRIPT.value,
        MetadataFieldsEnum.BUILD_SCRIPT.value,
        MetadataFieldsEnum.BUG_ID.value,
        MetadataFieldsEnum.LANGUAGE.value,
        MetadataFieldsEnum.PASSING_TEST_IDS.value,
        MetadataFieldsEnum.FAILING_TEST_IDS.value,
    ],
    "additionalProperties": True,
}

"""
General Section Schema
"""
general_section_schema = {
    "type": "array",
    "minItems": 1,
    "items": bug_info_schema,
}
