import json
import multiprocessing
import os
import pathlib
import sys
from argparse import Namespace
from typing import Any
from typing import Dict

from app.core import emitter
from app.core import utilities
from app.core import values
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


def load_configuration_details(config_file_path: str):
    emitter.normal("loading profile setup")
    json_data = None
    if os.path.isfile(config_file_path):
        with open(config_file_path, "r") as conf_file:
            json_data = json.load(conf_file)
    else:
        utilities.error_exit("Configuration file does not exist")
    return json_data


def load_class(class_name: str):
    components = class_name.split(".")
    mod = __import__(components[0])
    for comp in components[1:]:
        mod = getattr(mod, comp)
    return mod


def load_tool(tool_name: str):
    task_type = values.task_type
    emitter.normal(f"loading {task_type} tool")
    # class_file_path = values.dir_tool_drivers + tool_name + ".py"
    tool_type = values.task_type
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
    emitter.normal("loading benchmark")
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
    raise Exception("Should not be reachable")


class Configurations:
    __config_file = None
    __email_config_file = None
    __default_config_values: Dict[str, Any] = {
        "depth": 3,
        "iteration-limit": 1,
        "patch-rank-limit": 5,
        "stack-size": 15000,
        "use-cache": False,
        "use-gpu": False,
        "use-container": True,
        "email-setup": False,
        "is-debug": False,
        "use-purge": False,
        "only-analyse": False,
        "only-setup": False,
        "rebuild-all": False,
        "rebuild-base": False,
        "subject-name": None,
        "benchmark-name": None,
        "dump-patches": False,
        "start-index": None,
        "end-index": None,
        "use-tui": False,
        "cpu-count": 1,
        "bug-id-list": [],
        "bug-index-list": [],
        "skip-index-list": [],
        "tool-list": [],
        "directories": {"data": "/data"},
        "profile-id-list": ["C1"],
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
        emitter.normal("reading profile values")
        emitter.normal("reading configuration values from arguments")
        flat_map = lambda f, xs: (y for ys in xs for y in f(ys))
        self.__runtime_config_values["task-type"] = arg_list.task_type
        if arg_list.config:
            self.__config_file = arg_list.config
            self.read_config_file()

        if arg_list.email_config:
            self.__runtime_config_values["email-setup"] = True
            self.__email_config_file = arg_list.email_config
            self.read_email_config_file()

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

        if arg_list.rebuild_all:
            self.__runtime_config_values["rebuild-all"] = True

        if arg_list.rebuild_base:
            self.__runtime_config_values["rebuild-base"] = True

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

        if arg_list.use_tui:
            self.__runtime_config_values["use-tui"] = True

        if arg_list.profile_id_list:
            self.__runtime_config_values["config-id-list"] = arg_list.profile_id_list

        if arg_list.bug_index:
            self.__runtime_config_values["bug-index-list"] = [arg_list.bug_index]
        if arg_list.bug_index_list:
            self.__runtime_config_values["bug-index-list"] = list(
                flat_map(
                    self.convert_range,
                    str(arg_list.bug_index_list).split(","),
                )
            )
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

        if arg_list.use_gpu:
            self.__runtime_config_values["use-gpu"] = arg_list.use_gpu

        if arg_list.profile_id_list:
            self.__runtime_config_values["profile-id-list"] = arg_list.profile_id_list

    def read_config_file(self):
        flat_map = lambda f, xs: (y for ys in xs for y in f(ys))
        config_info = {}
        if self.__config_file:
            config_info = json.load(self.__config_file)

        try:
            self.__runtime_config_values["benchmark-name"] = config_info[
                "benchmark-name"
            ]
            self.__runtime_config_values["tool-list"] = config_info["tool-list"]

        except KeyError as exc:
            raise ValueError(f"missing field in configuration file: {exc}")

        if "bug-index-list" in config_info:
            self.__runtime_config_values["bug-index-list"] = list(
                flat_map(
                    self.convert_range,
                    str(config_info["bug-index-list"]).split(","),
                )
            )

        optional_keys = [
            "subject-name",
            "tool-params",
            "use-purge",
            "use-container",
            "dir-data",
            "bug-id-list",
            "start-index",
            "end-index",
            "skip-index-list",
            "use-gpu",
            "profile-id-list",
            "docker-host",
        ]
        for key in optional_keys:
            if key in config_info:
                self.__runtime_config_values[key] = config_info[key]

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

    def print_configuration(self):
        for config_key, config_value in self.__runtime_config_values.items():
            emitter.configuration(config_key, config_value)

    def update_configuration(self):
        emitter.normal("updating configuration values")
        if not self.__runtime_config_values["only-setup"]:
            if not self.__runtime_config_values["tool-list"]:
                emitter.error("(invalid) --tool/-tool-list is missing")
                emitter.emit_help()
                exit(1)
        values.task_type = self.__runtime_config_values["task-type"]
        values.benchmark_name = self.__runtime_config_values["benchmark-name"]
        values.subject_name = self.__runtime_config_values["subject-name"]
        if values.subject_name:
            emitter.normal(
                "[info] running experiments for subject {}".format(values.subject_name)
            )
        values.file_meta_data = os.path.join(
            "benchmark", values.benchmark_name, "meta-data.json"
        )
        values.start_index = self.__runtime_config_values["start-index"]
        values.end_index = self.__runtime_config_values["end-index"]
        values.bug_index_list = self.__runtime_config_values.get("bug-index-list", [])
        values.skip_index_list = self.__runtime_config_values.get("skip-index-list", [])
        values.bug_id_list = self.__runtime_config_values.get("bug-id-list", [])
        values.profile_id_list = self.__runtime_config_values["profile-id-list"]
        values.use_tui = self.__runtime_config_values["use-tui"]

        if (
            values.start_index is None
            and values.end_index is None
            and not values.bug_id_list is None
            and not values.bug_index_list
            and values.subject_name is None
        ):
            emitter.warning(
                "[warning] experiment id is not specified, running all experiments"
            )

        values.only_setup = self.__runtime_config_values["only-setup"]
        values.only_analyse = self.__runtime_config_values["only-analyse"]
        values.use_container = self.__runtime_config_values["use-container"]
        values.dump_patches = self.__runtime_config_values["dump-patches"]
        values.rebuild_all = self.__runtime_config_values["rebuild-all"]
        values.use_gpu = self.__runtime_config_values["use-gpu"]
        values.email_setup = self.__runtime_config_values["email-setup"]
        values.cpus = min(
            multiprocessing.cpu_count(), self.__runtime_config_values["cpu-count"]
        )

        values.docker_host = self.__runtime_config_values.get(
            "docker-host", values.docker_host
        )
        values.rebuild_base = self.__runtime_config_values["rebuild-base"]
        values.debug = self.__runtime_config_values["is-debug"]
        values.tool_list = self.__runtime_config_values["tool-list"]
        sys.setrecursionlimit(values.default_stack_size)
