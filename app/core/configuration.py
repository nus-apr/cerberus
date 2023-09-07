import json
import multiprocessing
import os
import pathlib
import sys
from argparse import Namespace
from os.path import join
from typing import Any
from typing import Dict
from typing import List

from app.core import emitter
from app.core import utilities
from app.core import values
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


def load_profiles(profile_file_path: str) -> Dict[str, Dict[str, Any]]:
    json_data = None
    if os.path.isfile(profile_file_path):
        with open(profile_file_path, "r") as conf_file:
            json_data = json.load(conf_file)
    else:
        utilities.error_exit("Configuration file does not exist")
    if type(json_data) is not dict:
        utilities.error_exit(
            "The collection of profiles should be in a dictionary where the id is the key"
        )
    return json_data


def load_class(class_name: str):
    components = class_name.split(".")
    mod = __import__(components[0])
    for comp in components[1:]:
        mod = getattr(mod, comp)
    return mod


def load_tool(tool_name: str, tool_type: str) -> AbstractTool:
    emitter.normal(f"\t[framework] loading {tool_type} tool {tool_name}")
    tool_directory = f"{values.dir_tool_drivers}/{tool_type}"
    existing_tool_list = [
        (str(x).split("/")[-1], str(x).split("/")[-2])
        for x in pathlib.Path(tool_directory).rglob("*.py")
    ]
    tool_class_name = None
    tool_language = None

    for tool, language in existing_tool_list:
        if tool.lower().replace(".py", "") == tool_name.lower():
            tool_class_name = tool.replace(".py", "")
            tool_language = language
    if not tool_class_name:
        utilities.error_exit(f"Unknown tool name {tool_name} for type {tool_type}")
    else:
        mod = __import__(
            f"app.drivers.tools.{tool_type}.{tool_language}", fromlist=[tool_class_name]
        )
        tool_class = getattr(mod, tool_class_name)
        initializer = getattr(tool_class, tool_class_name)
        return initializer()


def load_benchmark(benchmark_name: str) -> AbstractBenchmark:
    emitter.normal("\t[framework] loading benchmark {}".format(benchmark_name))
    # class_file_path = values.dir_benchmark_drivers + benchmark_name + ".py"

    existing_benchmark_list = [
        (str(x).split("/")[-1], str(x).split("/")[-2])
        for x in pathlib.Path(values.dir_benchmark_drivers).rglob("*.py")
    ]

    benchmark_class_name = None
    benchmark_language = None
    for benchmark, language in existing_benchmark_list:
        if "Abstract" in benchmark or "init" in benchmark:
            continue
        if benchmark.lower().replace(".py", "") == benchmark_name.lower():
            benchmark_class_name = benchmark.replace(".py", "")
            benchmark_language = language

    if not benchmark_class_name:
        utilities.error_exit("Unknown benchmark name", benchmark_name)
    else:
        mod = __import__(
            f"app.drivers.benchmarks.{benchmark_language}",
            fromlist=[benchmark_class_name],
        )
        benchmark_class = getattr(mod, str(benchmark_class_name))
        initializer = getattr(benchmark_class, str(benchmark_class_name))
        return initializer()


class Configurations:
    __email_config_file = open(join(values.dir_config, "email.json"))
    __slack_config_file = open(join(values.dir_config, "slack.json"))
    __discord_config_file = open(join(values.dir_config, "discord.json"))
    __default_config_values: Dict[str, Any] = {
        "depth": 3,
        "iteration-limit": 1,
        "patch-rank-limit": 5,
        "stack-size": 15000,
        "use-cache": False,
        "use-gpu": False,
        "use-container": True,
        "secure-hash": False,
        "is-debug": False,
        "use-purge": False,
        "only-analyse": False,
        "only-setup": False,
        "rebuild-all": False,
        "rebuild-base": False,
        "compact-results": False,
        "subject-name": None,
        "benchmark-name": None,
        "dump-patches": False,
        "start-index": None,
        "end-index": None,
        "parallel": False,
        "has-config-file": False,
        "cpu-count": 1,
        "runs": 1,
        "bug-id-list": [],
        "bug-index-list": [],
        "skip-index-list": [],
        "tool-list": [],
        "tool-params": "",
        "tool-tag": "",
        "directories": {"data": "/data"},
        "repair-profile-id-list": ["TP1"],
        "container-profile-id-list": ["CP1"],
        "use-latest-image": False,
    }
    __runtime_config_values = __default_config_values

    def convert_range(self, x):
        parts = x.split("-")
        if len(parts) == 1:
            return [int(parts[0])]
        if len(parts) == 0:
            return []
        start = 1 if parts[0] == "" else int(parts[0])
        end = 9999 if parts[1] == "" else int(parts[1])
        return range(start, end + 1)

    def read_arg_list(self, arg_list: Namespace):
        emitter.normal("\t[framework] reading configuration values from arguments")
        flat_map = lambda f, xs: (y for ys in xs for y in f(ys))
        self.__runtime_config_values["task-type"] = arg_list.task_type

        if arg_list.docker_host:
            self.__runtime_config_values["docker-host"] = arg_list.docker_host

        if arg_list.benchmark:
            self.__runtime_config_values["benchmark-name"] = arg_list.benchmark

        if arg_list.tool:
            self.__runtime_config_values["tool-list"] = [arg_list.tool]
        elif arg_list.tool_list:
            self.__runtime_config_values["tool-list"] = arg_list.tool_list

        if arg_list.subject:
            self.__runtime_config_values["subject-name"] = arg_list.subject

        if arg_list.tool_param:
            self.__runtime_config_values["tool-params"] = arg_list.tool_param

        if arg_list.tool_tag:
            self.__runtime_config_values["tool-tag"] = arg_list.tool_tag

        if arg_list.rebuild_all:
            self.__runtime_config_values["rebuild-all"] = True

        if arg_list.rebuild_base:
            self.__runtime_config_values["rebuild-base"] = True

        if arg_list.config_file:
            self.__runtime_config_values["has-config-file"] = True

        if arg_list.secure_hash:
            self.__runtime_config_values["secure-hash"] = True

        if arg_list.debug:
            self.__runtime_config_values["is-debug"] = True

        if arg_list.cache:
            self.__runtime_config_values["use-cache"] = True
        if arg_list.purge:
            self.__runtime_config_values["use-purge"] = True
        if arg_list.only_analyse:
            self.__runtime_config_values["only-analyse"] = True
        if not arg_list.use_container or arg_list.use_local:
            self.__runtime_config_values["use-container"] = False

        if arg_list.data_dir:
            self.__runtime_config_values["dir-data"] = arg_list.data_dir

        if arg_list.only_setup:
            self.__runtime_config_values["only-setup"] = True

        if arg_list.use_latest_image:
            self.__runtime_config_values["use-latest-image"] = True

        if arg_list.parallel:
            self.__runtime_config_values["parallel"] = True

        if arg_list.bug_index:
            self.__runtime_config_values["bug-index-list"] = [arg_list.bug_index]
        if arg_list.bug_index_list:
            self.__runtime_config_values["bug-index-list"] = list(
                flat_map(
                    self.convert_range,
                    str(arg_list.bug_index_list).split(","),
                )
            )
        if arg_list.runs:
            self.__runtime_config_values["runs"] = arg_list.runs
        if arg_list.cpu_count:
            self.__runtime_config_values["cpu-count"] = arg_list.cpu_count

        if arg_list.bug_id:
            self.__runtime_config_values["bug-id-list"] = [arg_list.bug_id]
        if arg_list.bug_id_list:
            self.__runtime_config_values["bug-id-list"] = arg_list.bug_id_list

        if arg_list.start_index:
            self.__runtime_config_values["start-index"] = int(arg_list.start_index)
        if arg_list.end_index:
            self.__runtime_config_values["end-index"] = int(arg_list.end_index)

        if arg_list.skip_index_list:
            self.__runtime_config_values["skip-index-list"] = str(
                arg_list.skip_index_list
            ).split(",")

        if arg_list.compact_results:
            self.__runtime_config_values["compact-results"] = arg_list.compact_results

        if arg_list.use_gpu:
            self.__runtime_config_values["use-gpu"] = arg_list.use_gpu

        if arg_list.repair_profile_id_list:
            self.__runtime_config_values[
                "repair-profile-id-list"
            ] = arg_list.repair_profile_id_list

        if arg_list.container_profile_id_list:
            self.__runtime_config_values[
                "container-profile-id-list"
            ] = arg_list.container_profile_id_list

    def read_slack_config_file(self):
        slack_config_info = {}
        if self.__slack_config_file:
            slack_config_info = json.load(self.__slack_config_file)
        for key, value in slack_config_info.items():
            if key in values.slack_configuration and type(value) == type(
                values.slack_configuration[key]
            ):
                values.slack_configuration[key] = value
            else:
                utilities.error_exit(
                    "[error] Unknown key {} or invalid type of value".format(key)
                )

        if values.slack_configuration["enabled"] and not (
            values.slack_configuration["hook_url"]
            or (
                values.slack_configuration["oauth_token"]
                and values.slack_configuration["channel"]
            )
        ):
            utilities.error_exit("[error] invalid configuration for slack.")

    def read_email_config_file(self):
        email_config_info = {}
        if self.__email_config_file:
            email_config_info = json.load(self.__email_config_file)
        for key, value in email_config_info.items():
            if key in values.email_configuration and type(value) == type(
                values.email_configuration[key]
            ):
                values.email_configuration[key] = value
            else:
                utilities.error_exit(
                    "[error] unknown key {} or invalid type of value".format(key)
                )
        if values.email_configuration["enabled"] and not (
            values.email_configuration["username"]
            and values.email_configuration["password"]
            and values.email_configuration["host"]
        ):
            utilities.error_exit("[error] invalid configuration for email.")

    def read_discord_config_file(self):
        discord_config_info = {}
        if self.__discord_config_file:
            discord_config_info = json.load(self.__discord_config_file)

        for key, value in discord_config_info.items():
            if key in values.discord_configuration and type(value) == type(
                values.discord_configuration[key]
            ):
                values.discord_configuration[key] = value
            else:
                utilities.error_exit(
                    "[error] unknown key {} or invalid type of value".format(key)
                )
        if values.discord_configuration["enabled"] and not (
            values.discord_configuration["hook_url"]
        ):
            utilities.error_exit("[error] invalid configuration for discord.")

    def print_configuration(self):
        for config_key, config_value in self.__runtime_config_values.items():
            if config_value is not None:
                emitter.configuration(config_key, config_value)

    def update_configuration(self):
        emitter.normal("\t[framework] updating configuration values")
        values.task_type.set(self.__runtime_config_values["task-type"])
        values.only_setup = self.__runtime_config_values["only-setup"]
        if values.task_type.get() == "prepare":
            values.only_setup = True
        if (
            not values.only_setup
            and not self.__runtime_config_values["has-config-file"]
        ):
            if not self.__runtime_config_values["tool-list"]:
                emitter.error("[invalid] --tool/-tool-list is missing")
                emitter.emit_help()
                exit(1)
        values.benchmark_name = self.__runtime_config_values["benchmark-name"]
        values.subject_name = self.__runtime_config_values["subject-name"]
        if values.subject_name:
            emitter.normal(
                "\t[framework] Running experiments for subject {}".format(
                    values.subject_name
                )
            )
        values.start_index = self.__runtime_config_values["start-index"]
        values.end_index = self.__runtime_config_values["end-index"]
        values.bug_index_list = self.__runtime_config_values.get("bug-index-list", [])
        values.skip_index_list = self.__runtime_config_values.get("skip-index-list", [])
        values.bug_id_list = self.__runtime_config_values.get("bug-id-list", [])
        values.task_profile_id_list = self.__runtime_config_values[
            "repair-profile-id-list"
        ]
        values.container_profile_id_list = self.__runtime_config_values[
            "container-profile-id-list"
        ]
        values.use_parallel = self.__runtime_config_values["parallel"]
        values.use_latest_image = self.__runtime_config_values["use-latest-image"]

        if (
            values.start_index is None
            and values.end_index is None
            and not values.bug_id_list is None
            and not values.bug_index_list
            and values.subject_name is None
        ):
            emitter.warning(
                "\t[framework][warning] experiment id is not specified, running all experiments"
            )

        values.compact_results = self.__runtime_config_values["compact-results"]
        values.only_analyse = self.__runtime_config_values["only-analyse"]
        values.use_container = self.__runtime_config_values["use-container"]
        values.dump_patches = self.__runtime_config_values["dump-patches"]
        values.rebuild_all = self.__runtime_config_values["rebuild-all"]
        values.use_gpu = self.__runtime_config_values["use-gpu"]
        values.use_purge = self.__runtime_config_values["use-purge"]
        values.runs = max(1, self.__runtime_config_values["runs"])
        values.use_cache = self.__runtime_config_values["use-cache"]
        values.cpus = max(
            1,
            min(
                multiprocessing.cpu_count() - 2,
                self.__runtime_config_values["cpu-count"],
            ),
        )

        values.docker_host = self.__runtime_config_values.get(
            "docker-host", values.docker_host
        )
        values.rebuild_base = self.__runtime_config_values["rebuild-base"]
        values.debug = self.__runtime_config_values["is-debug"]
        values.secure_hash = self.__runtime_config_values["secure-hash"]
        values.tool_list = self.__runtime_config_values["tool-list"]

        values.tool_params = self.__runtime_config_values["tool-params"]
        values.tool_tag = self.__runtime_config_values["tool-tag"]

        sys.setrecursionlimit(values.default_stack_size)
