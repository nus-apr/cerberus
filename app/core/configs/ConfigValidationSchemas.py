from typing import Any
from typing import cast
from typing import Dict

from app.core.configs.ConfigFieldsEnum import ConfigFieldsEnum

"""
General Section Schema
"""
general_section_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.PARALLEL_MODE.value: {"type": "boolean"},
        ConfigFieldsEnum.UI_MODE.value: {"type": "boolean"},
        ConfigFieldsEnum.DEBUG_MODE.value: {"type": "boolean"},
        ConfigFieldsEnum.SECURE_HASH.value: {"type": "boolean"},
        ConfigFieldsEnum.CPUS.value: {"type": "integer", "minimum": 2},
        ConfigFieldsEnum.GPUS.value: {"type": "integer", "minimum": 0},
    },
    "required": [
        ConfigFieldsEnum.PARALLEL_MODE.value,
        ConfigFieldsEnum.UI_MODE.value,
        ConfigFieldsEnum.DEBUG_MODE.value,
        ConfigFieldsEnum.SECURE_HASH.value,
    ],
    "additionalProperties": False,
}

"""
Profiles Section Schema
"""
# task profile schema
task_profile_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.PROFILE_ID.value: {"type": "string"},
        ConfigFieldsEnum.TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.FUZZ_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.REPAIR_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.LOCALIZE_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.VALIDATE_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.SELECT_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.COMPOSITE_TIMEOUT.value: {"type": "number", "minimum": 0},
        ConfigFieldsEnum.FAULT_LOCATION.value: {"type": "string"},
        ConfigFieldsEnum.PASSING_TEST_RATIO.value: {
            "type": "number",
            "minimum": 0,
            "maximum": 1,
        },
        ConfigFieldsEnum.PASSING_TEST_LIMIT.value: {
            "type": "number",
            "minimum": 0,
        },
        ConfigFieldsEnum.FAILING_TEST_LIMIT.value: {
            "type": "number",
            "minimum": 0,
        },
        ConfigFieldsEnum.PATCH_DIRECTORY.value: {"type": "string"},
    },
    "required": [
        ConfigFieldsEnum.PROFILE_ID.value,
        ConfigFieldsEnum.TIMEOUT.value,
        ConfigFieldsEnum.FAULT_LOCATION.value,
        ConfigFieldsEnum.PASSING_TEST_RATIO.value,
    ],
    "additionalProperties": False,
}

# container profile schema
container_profile_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.PROFILE_ID.value: {"type": "string"},
        ConfigFieldsEnum.CPU_COUNT.value: {"type": "integer", "minimum": 1},
        ConfigFieldsEnum.MEM_LIMIT.value: {
            "type": "string",
            "pattern": "^[1-9][0-9]*[gG]$",
        },
        ConfigFieldsEnum.ENABLE_NETWORK.value: {"type": "boolean"},
        ConfigFieldsEnum.GPU_COUNT.value: {"type": "integer", "minimum": 0},
    },
    "required": [
        ConfigFieldsEnum.PROFILE_ID.value,
        ConfigFieldsEnum.CPU_COUNT.value,
        ConfigFieldsEnum.MEM_LIMIT.value,
        ConfigFieldsEnum.ENABLE_NETWORK.value,
    ],
    "additionalProperties": False,
}

profiles_section_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.TASK_PROFILES_LIST.value: {
            "type": "array",
            "minItems": 1,
            "items": task_profile_schema,
        },
        ConfigFieldsEnum.CONTAINER_PROFILES_LIST.value: {
            "type": "array",
            "minItems": 1,
            "items": container_profile_schema,
        },
    },
    "required": [
        ConfigFieldsEnum.TASK_PROFILES_LIST.value,
        ConfigFieldsEnum.CONTAINER_PROFILES_LIST.value,
    ],
    "additionalProperties": False,
}

"""
Notifiers Section Schema
"""
email_config_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.ENABLE.value: {"type": "boolean"},
        ConfigFieldsEnum.USERNAME.value: {"type": "string"},
        ConfigFieldsEnum.PASSWORD.value: {"type": "string"},
        ConfigFieldsEnum.HOST.value: {"type": "string"},
        ConfigFieldsEnum.PORT.value: {"type": "integer"},
        ConfigFieldsEnum.SSL_FROM_START.value: {"type": "boolean"},
        ConfigFieldsEnum.RECIPIENTS.value: {
            "type": "array",
            "items": {"type": "string"},
            "minItems": 1,
        },
    },
    "required": [
        ConfigFieldsEnum.ENABLE.value,
        ConfigFieldsEnum.USERNAME.value,
        ConfigFieldsEnum.PASSWORD.value,
        ConfigFieldsEnum.HOST.value,
        ConfigFieldsEnum.PORT.value,
        ConfigFieldsEnum.SSL_FROM_START.value,
        ConfigFieldsEnum.RECIPIENTS.value,
    ],
    "additionalProperties": False,
}

slack_config_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.ENABLE.value: {"type": "boolean"},
        ConfigFieldsEnum.HOOK_URL.value: {"type": "string"},
        ConfigFieldsEnum.OAUTH_TOKEN.value: {"type": "string"},
        ConfigFieldsEnum.CHANNEL.value: {"type": "string"},
    },
    "required": [
        ConfigFieldsEnum.ENABLE.value,
        ConfigFieldsEnum.HOOK_URL.value,
        ConfigFieldsEnum.OAUTH_TOKEN.value,
        ConfigFieldsEnum.CHANNEL.value,
    ],
    "additionalProperties": False,
}

discord_config_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.ENABLE.value: {"type": "boolean"},
        ConfigFieldsEnum.HOOK_URL.value: {"type": "string"},
    },
    "required": [
        ConfigFieldsEnum.ENABLE.value,
        ConfigFieldsEnum.HOOK_URL.value,
    ],
    "additionalProperties": False,
}

notifies_section_schema = {
    "type": "object",
    "properties": {
        ConfigFieldsEnum.EMAIL.value: email_config_schema,
        ConfigFieldsEnum.SLACK.value: slack_config_schema,
        ConfigFieldsEnum.DISCORD.value: discord_config_schema,
    },
    "additionalProperties": False,
}

"""
Tasks Chunks Section Schema
"""
task_default_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Task Default Config",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.COMPACT_RESULTS.value: {"type": "boolean"},
        ConfigFieldsEnum.DUMP_PATCHES.value: {"type": "boolean"},
        ConfigFieldsEnum.DOCKER_HOST.value: {"type": "string"},
        ConfigFieldsEnum.ONLY_ANALYSE.value: {"type": "boolean"},
        ConfigFieldsEnum.ONLY_SETUP.value: {"type": "boolean"},
        ConfigFieldsEnum.ONLY_INSTRUMENT.value: {"type": "boolean"},
        ConfigFieldsEnum.ONLY_TEST.value: {"type": "boolean"},
        ConfigFieldsEnum.REBUILD_ALL.value: {"type": "boolean"},
        ConfigFieldsEnum.REBUILD_BASE.value: {"type": "boolean"},
        ConfigFieldsEnum.USE_CACHE.value: {"type": "boolean"},
        ConfigFieldsEnum.USE_CONTAINER.value: {"type": "boolean"},
        ConfigFieldsEnum.USE_GPU.value: {"type": "boolean"},
        ConfigFieldsEnum.USE_PURGE.value: {"type": "boolean"},
        ConfigFieldsEnum.USE_SUBJECT_AS_BASE.value: {"type": "boolean"},
        ConfigFieldsEnum.CONTAINER_PROFILE_ID_LIST.value: {
            "type": "array",
            "minItems": 1,
            "items": {"type": "string"},
        },
        ConfigFieldsEnum.TASK_PROFILE_ID_LIST.value: {
            "type": "array",
            "minItems": 1,
            "items": {"type": "string"},
        },
        ConfigFieldsEnum.RUNS.value: {
            "type": "number",
            "minimum": 1,
        },
    },
    "required": [
        ConfigFieldsEnum.CONTAINER_PROFILE_ID_LIST.value,
        ConfigFieldsEnum.TASK_PROFILE_ID_LIST.value,
    ],
    "additionalProperties": False,
}

benchmark_config_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Benchmark Config",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.NAME.value: {"type": "string"},
        ConfigFieldsEnum.BUG_ID_LIST.value: {
            "type": "array",
            "items": {"type": "string"},
            "minItems": 1,
        },
        ConfigFieldsEnum.BUG_SUBJECTS_LIST.value: {
            "minItems": 1,
            "type": "array",
            "items": {"type": "string"},
        },
        ConfigFieldsEnum.BUG_ID_SKIP_LIST.value: {
            "minItems": 1,
            "type": "array",
            "items": {"type": "string"},
        },
    },
    "required": [ConfigFieldsEnum.NAME.value],
    "oneOf": [
        {"required": [ConfigFieldsEnum.BUG_ID_LIST.value]},
        {"required": [ConfigFieldsEnum.BUG_SUBJECTS_LIST.value]},
    ],
    "additionalProperties": False,
}

tool_config_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Tool Config",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.NAME.value: {"type": "string"},
        ConfigFieldsEnum.PARAMS.value: {"type": "string"},
        ConfigFieldsEnum.TAG.value: {"type": "string"},
        ConfigFieldsEnum.IMAGE.value: {"type": "string"},
        ConfigFieldsEnum.IGNORE.value: {"type": "boolean"},
        ConfigFieldsEnum.HASH_DIGEST.value: {"type": "string"},
        ConfigFieldsEnum.LOCAL.value: {"type": "boolean"},
    },
    "required": [ConfigFieldsEnum.NAME.value],
    "additionalProperties": True,
}

composite_sequence_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Composite Sequence",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.FUZZ.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.ANALYZE.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.CRASH_ANALYZE.value: {
            "type": "array",
            "items": tool_config_schema,
        },
        ConfigFieldsEnum.ITERATIVE_REPAIR.value: {
            "type": "array",
            "items": tool_config_schema,
        },
        ConfigFieldsEnum.SLICE.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.LOCALIZE.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.REPAIR.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.VALIDATE.value: {"type": "array", "items": tool_config_schema},
        ConfigFieldsEnum.SELECT.value: {"type": "array", "items": tool_config_schema},
    },
    "additionalProperties": False,
}


tasks_chunks_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Tasks Chunks Config",
    "type": "object",
    "properties": {
        **cast(Dict[str, Any], task_default_schema["properties"]),
        ConfigFieldsEnum.TYPE.value: {"type": "string"},
        ConfigFieldsEnum.COMPOSITE_SEQUENCE.value: composite_sequence_schema,
        ConfigFieldsEnum.BENCHMARKS.value: {
            "type": "array",
            "minItems": 1,
            "items": benchmark_config_schema,
        },
        ConfigFieldsEnum.TOOLS.value: {
            "type": "array",
            "minItems": 1,
            "items": tool_config_schema,
        },
    },
    "required": [
        ConfigFieldsEnum.TYPE.value,
        ConfigFieldsEnum.BENCHMARKS.value,
        ConfigFieldsEnum.TOOLS.value,
    ],
    "additionalProperties": False,
}

tasks_data_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Tasks Data Config",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.DEFAULT_CONFIG.value: task_default_schema,
        ConfigFieldsEnum.TASKS_CHUNKS.value: {
            "type": "array",
            "minItems": 1,
            "items": tasks_chunks_schema,
        },
    },
    "required": [
        ConfigFieldsEnum.DEFAULT_CONFIG.value,
        ConfigFieldsEnum.TASKS_CHUNKS.value,
    ],
    "additionalProperties": False,
}

"""
Config Schema
"""
config_validation_schema = {
    "$schema": "http://json-schema.org/draft-07/schema#",
    "title": "Config",
    "type": "object",
    "properties": {
        ConfigFieldsEnum.GENERAL.value: general_section_schema,
        ConfigFieldsEnum.PROFILES.value: profiles_section_schema,
        ConfigFieldsEnum.NOTIFIERS.value: notifies_section_schema,
        ConfigFieldsEnum.TASKS_DATA.value: tasks_data_schema,
    },
    "required": [
        ConfigFieldsEnum.GENERAL.value,
        ConfigFieldsEnum.PROFILES.value,
        ConfigFieldsEnum.TASKS_DATA.value,
    ],
    "additionalProperties": False,
}
