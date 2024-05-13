import json
import multiprocessing
import os
import pathlib
import sys
from argparse import Namespace
from copy import deepcopy
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import Iterable
from typing import List

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.configs.Config import Config
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.task.typing.TaskList import TaskList
from app.core.task.typing.TaskType import compare_types
from app.core.task.typing.TaskType import CompositeTaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.MockTool import MockTool


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


def load_class(class_name: str) -> Any:
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
        return cast(AbstractTool, initializer())


def load_benchmark(benchmark_name: str) -> AbstractBenchmark:
    if benchmark_name is None:
        utilities.error_exit("No benchmark name is specified")
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
        return cast(AbstractBenchmark, initializer())


def process_overrides(parsed_args: Namespace, config: Config) -> None:
    if parsed_args.debug:
        config.general.debug_mode = True
    if parsed_args.secure_hash:
        config.general.secure_hash = True
    if parsed_args.parallel:
        config.general.parallel_mode = True
    if parsed_args.cpu_count:
        config.general.cpus = parsed_args.cpu_count
    if parsed_args.gpu_count:
        config.general.gpus = parsed_args.gpu_count
    if parsed_args.subsequence:
        start, end = parsed_args.subsequence.split("-")
        start = start.replace("_", "-")
        end = end.replace("_", "-")
        for chunk in config.tasks_configs_list:
            if chunk.task_config.task_type == "composite":
                for task_type, tools in cast(
                    Dict[CompositeTaskType, List[Dict[str, Any]]],
                    getattr(chunk.task_config, "composite_sequence"),
                ).items():
                    if not (
                        compare_types(task_type, start) >= 0
                        and compare_types(task_type, end) <= 0
                    ):
                        for tool_info in tools:
                            tool_info["ignore"] = True
    if parsed_args.rebuild_all:
        for x in config.tasks_configs_list:
            x.task_config.rebuild_all = True
    if parsed_args.rebuild_base:
        for x in config.tasks_configs_list:
            x.task_config.rebuild_base = True


class Configurations:
    __email_config_file = open(join(values.dir_config, "email.json"))
    __slack_config_file = open(join(values.dir_config, "slack.json"))
    __api_config_file = open(join(values.dir_config, "api.json"))
    __discord_config_file = open(join(values.dir_config, "discord.json"))
    __default_config_values: Dict[str, Any] = {
        "use-cache": False,
        "use-gpu": False,
        "use-container": True,
        "secure-hash": False,
        "is-debug": False,
        "use-purge": False,
        "only-analyse": False,
        "only-setup": False,
        "only-instrument": False,
        "only-test": False,
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
        "all-cpu-count": 1,
        "all-gpu-count": 0,
        # "task-cpu-count": 1,
        "runs": 1,
        "bug-id-list": [],
        "bug-index-list": [],
        "skip-index-list": [],
        "tool-list": [],
        "tool-params": "",
        "tool-tag": "",
        "special-meta": "",
        "directories": {"data": "/data"},
        "task-profile-id-list": ["TP1"],
        "container-profile-id-list": ["CP1"],
        "use-latest-image": False,
        "use-subject-as-base": False,
    }
    __runtime_config_values = __default_config_values

    def convert_range(self, x: str) -> Iterable[int]:
        parts = x.split("-")
        if len(parts) == 1:
            return [int(parts[0])]
        if len(parts) == 0:
            return []
        start = 1 if parts[0] == "" else int(parts[0])
        end = 9999 if parts[1] == "" else int(parts[1])
        return range(start, end + 1)

    def read_arg_list(self, arg_list: Namespace) -> None:
        emitter.normal("\t[framework] reading configuration values from arguments")

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

        if not arg_list.use_container or arg_list.use_local:
            self.__runtime_config_values["use-container"] = False

        if arg_list.data_dir:
            self.__runtime_config_values["dir-data"] = arg_list.data_dir

        if arg_list.only_analyse:
            self.__runtime_config_values["only-analyse"] = True

        if arg_list.only_setup:
            self.__runtime_config_values["only-setup"] = True

        if arg_list.only_test:
            self.__runtime_config_values["only-test"] = True

        if arg_list.only_instrument:
            self.__runtime_config_values["only-instrument"] = True

        if arg_list.use_latest_image:
            self.__runtime_config_values["use-latest-image"] = True

        if arg_list.subject_based:
            self.__runtime_config_values["use-subject-as-base"] = True

        if arg_list.parallel:
            self.__runtime_config_values["parallel"] = True

        if arg_list.bug_index:
            self.__runtime_config_values["bug-index-list"] = [arg_list.bug_index]

        if arg_list.bug_index_list:
            self.__runtime_config_values["bug-index-list"] = list(
                utilities.flat_map(
                    self.convert_range,
                    str(arg_list.bug_index_list).split(","),
                )
            )
        if arg_list.runs:
            self.__runtime_config_values["runs"] = arg_list.runs

        if arg_list.cpu_count:
            self.__runtime_config_values["all-cpu-count"] = arg_list.cpu_count

        if arg_list.gpu_count:
            self.__runtime_config_values["all-gpu-count"] = arg_list.gpu_count

        # if arg_list.task_cpu_count:
        #    self.__runtime_config_values["task-cpu-count"] = arg_list.task_cpu_count

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

        if arg_list.special_meta:
            self.__runtime_config_values["special-meta"] = arg_list.special_meta

        if arg_list.use_gpu:
            self.__runtime_config_values["use-gpu"] = arg_list.use_gpu

        if arg_list.task_profile_id_list:
            self.__runtime_config_values["task-profile-id-list"] = (
                arg_list.task_profile_id_list
            )

        if arg_list.container_profile_id_list:
            self.__runtime_config_values["container-profile-id-list"] = (
                arg_list.container_profile_id_list
            )

    def read_slack_config_file(self) -> None:
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

    def read_api_config_file(self) -> None:
        api_config_info = {}
        if self.__api_config_file:
            api_config_info = json.load(self.__api_config_file)
        for key, value in api_config_info.items():
            if key in values.api_configuration and type(value) == type(
                values.api_configuration[key]
            ):
                values.api_configuration[key] = value
            else:
                utilities.error_exit(
                    "[error] Unknown key {} or invalid type of value".format(key)
                )

    def read_email_config_file(self) -> None:
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

    def read_discord_config_file(self) -> None:
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

    def print_configuration(self) -> None:
        for config_key, config_value in self.__runtime_config_values.items():
            if config_value is not None:
                emitter.configuration(config_key, config_value)

    def filter_experiment_list(
        self, benchmark: AbstractBenchmark
    ) -> List[Dict[str, Any]]:
        filtered_list = []
        experiment_list = benchmark.get_list()
        for bug_index in range(1, benchmark.size + 1):
            experiment_item = experiment_list[bug_index - 1]
            subject_name = experiment_item[definitions.KEY_SUBJECT]
            bug_name = str(experiment_item[definitions.KEY_BUG_ID])
            if self.bug_id_list and bug_name not in self.bug_id_list:
                continue
            if self.bug_index_list and bug_index not in self.bug_index_list:
                continue
            if self.skip_index_list and str(bug_index) in self.skip_index_list:
                continue
            if self.start_index and bug_index < self.start_index:
                continue
            if self.subject_name and self.subject_name != subject_name:
                continue
            if self.end_index and bug_index > self.end_index:
                break
            filtered_list.append(experiment_item)
        return filtered_list

    def construct_task_list(self) -> TaskList:
        tool_list: List[AbstractTool] = self.get_tools()
        benchmark: AbstractBenchmark = self.get_benchmark()
        task_profiles: Dict[str, Dict[str, Any]] = self.get_task_profiles()
        container_profiles: Dict[str, Dict[str, Any]] = self.get_container_profiles()
        task_type = self.task_type

        if not task_type:
            utilities.error_exit("No task type defined")

        for task_profile_template in map(
            lambda task_profile_id: task_profiles[task_profile_id],
            self.task_profile_id_list,
        ):
            task_profile = deepcopy(task_profile_template)
            task_profile[definitions.KEY_TOOL_PARAMS] = self.tool_params
            task_profile[definitions.KEY_TOOL_TAG] = self.tool_tag
            for container_profile_template in map(
                lambda container_profile_id: container_profiles[container_profile_id],
                self.container_profile_id_list,
            ):
                task_config = TaskConfig(
                    task_type,
                    values.compact_results,
                    values.dump_patches,
                    values.docker_host,
                    values.only_analyse,
                    values.only_setup,
                    values.only_instrument,
                    values.only_test,
                    values.rebuild_all,
                    values.rebuild_base,
                    values.use_cache,
                    values.use_container,
                    values.use_gpu,
                    values.use_purge,
                    values.runs,
                )

                container_profile = deepcopy(container_profile_template)
                for experiment_item in self.filter_experiment_list(benchmark):
                    bug_index = experiment_item[definitions.KEY_ID]

                    for tool in tool_list:
                        yield (
                            task_config,
                            (
                                deepcopy(benchmark),
                                deepcopy(tool),
                                experiment_item,
                                task_profile,
                                container_profile,
                                bug_index,
                            ),
                        )

    def get_task_profiles(self) -> Dict[str, Dict[str, Any]]:
        emitter.normal("\t[framework] loading repair task profiles")
        task_profiles = load_profiles(values.file_task_profiles)
        for task_profile_id in self.task_profile_id_list:
            if task_profile_id not in task_profiles:
                utilities.error_exit(
                    "invalid task profile id {}".format(task_profile_id)
                )
        return task_profiles

    def get_container_profiles(self) -> Dict[str, Dict[str, Any]]:
        emitter.normal("\t[framework] loading container profiles")
        container_profiles = load_profiles(values.file_container_profiles)
        for container_profile_id in self.container_profile_id_list:
            if container_profile_id not in container_profiles:
                utilities.error_exit(
                    "invalid container profile id {}".format(container_profile_id)
                )
        return container_profiles

    def get_tools(self) -> List[AbstractTool]:
        tool_list: List[AbstractTool] = []
        if self.task_type == "prepare":
            return [MockTool()]

        for tool_name in self.tool_list:
            tool = load_tool(tool_name, self.task_type)
            if not values.only_analyse:
                tool.ensure_tool_exists()
            tool_list.append(tool)
        emitter.highlight(
            f"\t[framework] {self.task_type}-tool(s): "
            + " ".join([x.name for x in tool_list])
        )
        return tool_list

    def get_benchmark(self) -> AbstractBenchmark:
        benchmark = load_benchmark(self.benchmark_name.lower())
        emitter.highlight(f"\t[framework] {self.task_type}-benchmark: {benchmark.name}")
        return benchmark

    def update_configuration(self) -> None:
        emitter.normal("\t[framework] updating configuration values")
        self.task_type = self.__runtime_config_values["task-type"]
        values.task_type.set(self.__runtime_config_values["task-type"])
        values.only_setup = self.__runtime_config_values["only-setup"]
        if self.task_type == "prepare":
            values.only_setup = True
        if (
            not values.only_setup
            and not self.__runtime_config_values["has-config-file"]
        ):
            if not self.__runtime_config_values["tool-list"]:
                emitter.error("[invalid] --tool/-tool-list is missing")
                emitter.emit_help()
                exit(1)

        values.use_parallel = self.__runtime_config_values["parallel"]
        values.use_latest_image = self.__runtime_config_values["use-latest-image"]
        values.use_subject_as_base = self.__runtime_config_values["use-subject-as-base"]

        self.benchmark_name = self.__runtime_config_values["benchmark-name"]
        self.subject_name = self.__runtime_config_values["subject-name"]
        if self.subject_name:
            emitter.normal(
                "\t[framework] Running experiments for subject {}".format(
                    self.subject_name
                )
            )
        self.start_index = self.__runtime_config_values["start-index"]
        self.end_index = self.__runtime_config_values["end-index"]
        self.bug_index_list = self.__runtime_config_values.get("bug-index-list", [])
        self.skip_index_list = self.__runtime_config_values.get("skip-index-list", [])
        self.bug_id_list = self.__runtime_config_values.get("bug-id-list", [])
        self.task_profile_id_list = self.__runtime_config_values["task-profile-id-list"]
        self.container_profile_id_list = self.__runtime_config_values[
            "container-profile-id-list"
        ]
        if (
            self.start_index is None
            and self.end_index is None
            and not self.bug_id_list is None
            and not self.bug_index_list
            and self.subject_name is None
        ):
            emitter.warning(
                "\t[framework][warning] experiment id is not specified, running all experiments"
            )
        self.tool_list = self.__runtime_config_values["tool-list"]
        self.tool_params = self.__runtime_config_values["tool-params"]
        self.tool_tag = self.__runtime_config_values["tool-tag"]

        values.only_test = self.__runtime_config_values["only-test"]
        values.only_instrument = self.__runtime_config_values["only-instrument"]
        values.compact_results = self.__runtime_config_values["compact-results"]
        values.only_analyse = self.__runtime_config_values["only-analyse"]
        values.use_container = self.__runtime_config_values["use-container"]
        values.dump_patches = self.__runtime_config_values["dump-patches"]
        values.rebuild_all = self.__runtime_config_values["rebuild-all"]
        values.use_gpu = self.__runtime_config_values["use-gpu"]
        values.use_purge = self.__runtime_config_values["use-purge"]
        values.runs = max(1, self.__runtime_config_values["runs"])
        values.use_cache = self.__runtime_config_values["use-cache"]
        values.special_meta = self.__runtime_config_values["special-meta"]

        values.cpus = max(
            1,
            min(
                multiprocessing.cpu_count() - 2,
                self.__runtime_config_values["all-cpu-count"],
            ),
        )
        values.gpus = max(
            0,
            min(
                utilities.get_gpu_count(), self.__runtime_config_values["all-gpu-count"]
            ),
        )

        # values.cpu_task = max(1,self.__runtime_config_values["task-cpu-count"])
        values.docker_host = self.__runtime_config_values.get(
            "docker-host", values.docker_host
        )
        values.rebuild_base = self.__runtime_config_values["rebuild-base"]
        values.debug = self.__runtime_config_values["is-debug"]
        values.secure_hash = self.__runtime_config_values["secure-hash"]

        sys.setrecursionlimit(values.default_stack_size)

        # This function is valid after Python 3.11
        if sys.version_info.major == 3 and sys.version_info.minor >= 11:
            sys.set_int_max_str_digits(0)
